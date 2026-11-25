-- Prove2me | solution 1 for PandoraKnapsack.Skipping.compiled_dyadic_sampler
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:50:13.755252+00:00
-- url     : https://prove2.me/submissions/7cbb0dde-e01b-4785-86b0-529ac43d6ac9

import Theorems.Thm_PandoraKnapsack_Skipping_ArrayRAM_prepare_array_exec
import Theorems.Thm_PandoraKnapsack_Skipping_ArrayRAM_packing_array_exec
import Theorems.Thm_PandoraKnapsack_Skipping_ArrayRAM_sampling_array_exec
import Theorems.Thm_PandoraKnapsack_Skipping_ArrayRAM_compile_cost_sound

open PandoraKnapsack.Skipping PandoraKnapsack.Skipping.ArrayRAM

private theorem problem_size (n m T : ℕ) :
    timeRows n T + columnCount n m T + 2 ≤ (inputSize n m T + 2)^5 := by
  let S := inputSize n m T+2
  have hn : n ≤ S := by dsimp [S,inputSize]; omega
  have hm : m ≤ S := by dsimp [S,inputSize]; omega
  have hK : labelCount T ≤ S := by
    unfold labelCount
    split_ifs with h
    · dsimp [S,inputSize]; omega
    · have hl := Nat.lt_size.mpr (Nat.pow_log_le_self 2 h)
      dsimp [S,inputSize]; omega
  calc
    _ ≤ S+S+S*(S*S)+2 := by unfold timeRows columnCount; gcongr
    _ ≤ S^5 := by
      obtain ⟨v,hv⟩ : ∃ v, S = v+2 := ⟨inputSize n m T,rfl⟩
      rw [hv]; ring_nf; omega

private theorem enough_time (S e f a b c R D : ℕ) (hs : 2 ≤ S)
    (ha : a ≤ S^e) (hb : b ≤ (R+D+2)^f) (hc : c ≤ S^24) (hr : R+D+2 ≤ S^5) :
    7+(a+(b+c)) ≤ S^(e+5*f+24+4) := by
  let Q := S^(e+5*f+24)
  have hs1 : 1 ≤ S := by omega
  have h1 : 1 ≤ Q := Nat.one_le_pow _ _ hs1
  have hpow (u : ℕ) (h : u ≤ e+5*f+24) : S^u ≤ Q := Nat.pow_le_pow_right (by omega) h
  have hA := ha.trans (hpow e (by omega))
  have hB : b ≤ Q := by
    apply hb.trans ((Nat.pow_le_pow_left hr _).trans ?_)
    rw [← pow_mul]; exact hpow _ (by omega)
  have hC := hc.trans (hpow 24 (by omega))
  have h16 : 16 ≤ S^4 := by simpa using Nat.pow_le_pow_left hs 4
  calc
    _ ≤ Q*16 := by omega
    _ ≤ Q*S^4 := Nat.mul_le_mul_left _ h16
    _ = _ := (pow_add S _ _).symm

private theorem close_run {n m T : ℕ} (I : Instance n m T) (w : ℕ → ℝ) (P : Program)
    (B : ℕ) (z : Store) (σ : SkipList n m)
    (hc : Halted P (run I w P B) ∧ decodeOutput n m (run I w P B).core.mem =
      decodeOutput n m (fun t => z.out t.toNat))
    (ho : ∀ mem : ℤ → ℝ, (∀ r : ℕ, mem r = z.out r) → decodeOutput n m mem = some σ) :
    Halted P (run I w P B) ∧ decodeOutput n m (run I w P B).core.mem = some σ :=
  And.intro hc.1 (@Eq.trans _ _ (decodeOutput n m (fun t => z.out t.toNat)) _ hc.2
    (ho (fun t => z.out t.toNat) (fun _ => rfl)))

attribute [local irreducible] ArrayRAM.compile run decodeOutput Halted alg1Policy uniformAssignment

set_option maxHeartbeats 400000 in
theorem solution :
    ∃ (P : Program) (k : ℕ), ∀ (n m T : ℕ) (I : Instance n m T), IsValid I →
      let B := (inputSize n m T + 2)^k
      ∃ (d : ℕ) (lab : Fin d → Fin m × Fin (T+1)) (hB : n ≤ B),
        Function.Injective lab ∧
        (∀ i j (t : Fin (T+1)), dyadicPlan I i j t.val ≠ 0 → ∃ u, lab u = (j,t)) ∧
        ∀ ω : Fin B → unitInterval,
          Halted P (run I (extendDraws ω) P B) ∧
          decodeOutput n m (run I (extendDraws ω) P B).core.mem =
            some (alg1Policy (uniformAssignment hB lab (dyadicPlan I) ω)) := by
  obtain ⟨e, prepare_spec⟩ := prepare_array_exec
  obtain ⟨f, pack_spec⟩ := packing_array_exec
  let source : C := .seq Prepare.code (.seq packingCode samplingCode)
  let exponent := e+5*f+24+4
  refine ⟨compile source,exponent,?_⟩
  intro n m T I _hvalid
  let S := inputSize n m T + 2
  let B := S^exponent
  have hs : 2 ≤ S := by dsimp [S]; omega
  have hn : n ≤ S := by dsimp [S,inputSize]; omega
  have hB : n ≤ B := hn.trans (Nat.le_self_pow (show exponent ≠ 0 by dsimp [exponent]; omega) _)
  let lab := samplingLab m T
  let GoodLab : Prop := Function.Injective lab ∧
    ∀ (i : Fin n) (j : Fin m) (t : Fin (T+1)), dyadicPlan I i j t.val ≠ 0 →
      ∃ q, lab q = (j,t)
  have verified (u : Fin B → unitInterval) : GoodLab ∧
      Halted (compile source) (run I (extendDraws u) (compile source) B) ∧
      decodeOutput n m (run I (extendDraws u) (compile source) B).core.mem =
        some (alg1Policy (uniformAssignment hB lab (dyadicPlan I) u)) := by
    let w := extendDraws u
    obtain ⟨a,k₁,h₁,b₁,hi,hj,hL,hD,hR,hT,hlabels,hweights,hmatrix,hprofits,hd⟩ :=
      prepare_spec n m T I w
    obtain ⟨b,k₂,h₂,b₂,hvec,hns,hrs,htab,_,hdraws⟩ :=
      pack_spec I w a (packingRows I) (packingProfits I) hD hR hmatrix hprofits
    obtain ⟨hinj,hsupp,z,k₃,h₃,b₃,_,hout⟩ := sampling_array_exec I hB u b
      ((hns 0 (by decide)).trans hi) ((hns 1 (by decide)).trans hj)
      ((hns 2 (by decide)).trans hL) ((hrs 0 (by decide)).trans hT)
      (fun h => (congrFun (htab 0 (by decide) (by decide)) h.val).trans (hlabels h))
      (fun c => (congrFun (htab 1 (by decide) (by decide)) c.val).trans (hweights c))
      hvec (hdraws.trans hd)
    have exec : Exec I w source (initial n m T) z (k₁+(k₂+k₃)) := Exec.seq h₁ (Exec.seq h₂ h₃)
    have bound : 7+(k₁+(k₂+k₃)) ≤ B :=
      enough_time S e f _ _ _ _ _ hs b₁ b₂ b₃ (problem_size n m T)
    change GoodLab ∧ Halted (compile source) (run I w (compile source) B) ∧
      decodeOutput n m (run I w (compile source) B).core.mem =
        some (alg1Policy (uniformAssignment hB (samplingLab m T) (dyadicPlan I) u))
    refine And.intro (And.intro hinj hsupp) ?_
    exact close_run I w (compile source) B z
      (alg1Policy (uniformAssignment hB (samplingLab m T) (dyadicPlan I) u))
      (compile_cost_sound I w source z _ B exec bound) hout
  obtain ⟨hlabel,_⟩ := verified (fun _ => 0)
  exact ⟨m*labelCount T,lab,hB,hlabel.1,hlabel.2,fun u => (verified u).2⟩
