-- Prove2me | solution 1 for OracleStateHSP.theorem_4_10
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:50:27.539798+00:00
-- url     : https://prove2.me/submissions/7c05299e-3602-4c8b-a33d-fa34009545ae
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OracleStateHSP_QueryAlgorithm_outputProb
import Definitions.Def_OracleStateHSP_IsStateHSPInstance
import Definitions.Def_OracleStateHSP_SimonInst
import Definitions.Def_OracleStateHSP_hiddenSubgroup
import Definitions.Def_OracleStateHSP_flagZero
import Definitions.Def_OracleStateHSP_shiftRep
import Definitions.Def_OracleStateHSP_fracU
import Theorems.Thm_OracleStateHSP_family_isStateHSP
import Theorems.Thm_OracleStateHSP_fracOracle_unitary_prepares
import Theorems.Thm_OracleStateHSP_fracOracle_queryComplexity

open scoped ENNReal
open OracleStateHSP QAlgorithms

namespace AuxThm410

def toDef41Kind : QueryKind → QueryKind
  | .fwd => .fwd
  | .inv => .inv
  | .conj => .fwd
  | .transp => .inv

lemma toDef41Kind_isFwdOrInv (k : QueryKind) : (toDef41Kind k).IsForwardOrInverse := by
  cases k <;> simp [toDef41Kind, QueryKind.IsForwardOrInverse]

lemma apply_toDef41Kind_of_real {Q : Type*} (k : QueryKind) (U : Matrix Q Q ℂ)
    (hreal : ∀ p q, (U p q).im = 0) :
    (toDef41Kind k).apply U = k.apply U := by
  have hmap : U.map star = U := by
    ext p q
    simp only [Matrix.map_apply]
    exact Complex.conj_eq_iff_im.mpr (hreal p q)
  have htr : U.transpose = U.conjTranspose := by
    ext p q
    simp only [Matrix.transpose_apply, Matrix.conjTranspose_apply]
    symm
    exact Complex.conj_eq_iff_im.mpr (hreal q p)
  cases k
  · rfl
  · rfl
  · exact hmap.symm
  · exact htr.symm

lemma queryOp_one {Q S W : Type*} [DecidableEq Q] [DecidableEq S] [DecidableEq W] :
    queryOp (S := S) (W := W) .fwd (1 : Matrix Q Q ℂ) = 1 := by
  ext p q
  rcases p with s1 | ⟨q1, w1⟩ <;> rcases q with s2 | ⟨q2, w2⟩
  · simp [queryOp, QueryKind.apply, Matrix.one_apply]
  · simp [queryOp]
  · simp [queryOp]
  · simp only [queryOp, QueryKind.apply, Matrix.fromBlocks_apply₂₂, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Sum.inr.injEq, Prod.ext_iff]
    by_cases hq : q1 = q2
    · subst hq
      by_cases hw : w1 = w2 <;> simp [hw]
    · simp [hq]

lemma queryOp_fwd_mul {Q S W : Type*} [Fintype Q] [Fintype S] [Fintype W]
    [DecidableEq Q] [DecidableEq S] [DecidableEq W] (M N : Matrix Q Q ℂ) :
    queryOp (S := S) (W := W) .fwd (M * N) =
      queryOp .fwd M * queryOp .fwd N := by
  simp only [queryOp, QueryKind.apply]
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  unfold Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul, one_mul]

lemma queryOp_inv_mul {Q S W : Type*} [Fintype Q] [Fintype S] [Fintype W]
    [DecidableEq Q] [DecidableEq S] [DecidableEq W] (M N : Matrix Q Q ℂ) :
    queryOp (S := S) (W := W) .inv (M * N) =
      queryOp .inv N * queryOp .inv M := by
  simp only [queryOp, QueryKind.apply, Matrix.conjTranspose_mul]
  rw [Matrix.fromBlocks_multiply]
  simp only [mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  congr 1
  unfold Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul, one_mul]

lemma queryOp_star_fwd {Q S W : Type*} [DecidableEq S] [DecidableEq W] (M : Matrix Q Q ℂ) :
    star (queryOp (S := S) (W := W) .fwd M) = queryOp .inv M := by
  ext p q
  rcases p with s1 | ⟨q1, w1⟩ <;> rcases q with s2 | ⟨q2, w2⟩
  · simp [queryOp, Matrix.star_apply, Matrix.one_apply, eq_comm]
  · simp [queryOp, Matrix.star_apply]
  · simp [queryOp, Matrix.star_apply]
  · simp only [queryOp, QueryKind.apply, Matrix.star_apply, Matrix.fromBlocks_apply₂₂,
      Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, star_mul']
    by_cases hw : w2 = w1
    · subst hw; simp
    · have hw' : w1 ≠ w2 := Ne.symm hw
      simp [hw, hw']

lemma star_mem_unitary {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ}
    (hM : M ∈ Matrix.unitaryGroup ι ℂ) : star M ∈ Matrix.unitaryGroup ι ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', star_star]
  exact Matrix.mem_unitaryGroup_iff.mp hM

lemma queryOp_fwd_unitary {Q S W : Type*} [Fintype Q] [Fintype S] [Fintype W]
    [DecidableEq Q] [DecidableEq S] [DecidableEq W] {M : Matrix Q Q ℂ}
    (hM : M ∈ Matrix.unitaryGroup Q ℂ) :
    queryOp (S := S) (W := W) .fwd M ∈ Matrix.unitaryGroup (S ⊕ (Q × W)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hM ⊢
  rw [queryOp_star_fwd]
  have heq : queryOp (S := S) (W := W) .inv M = queryOp .fwd (star M) := rfl
  rw [heq, ← queryOp_fwd_mul, hM, queryOp_one]

lemma queryOp_inv_unitary {Q S W : Type*} [Fintype Q] [Fintype S] [Fintype W]
    [DecidableEq Q] [DecidableEq S] [DecidableEq W] {M : Matrix Q Q ℂ}
    (hM : M ∈ Matrix.unitaryGroup Q ℂ) :
    queryOp (S := S) (W := W) .inv M ∈ Matrix.unitaryGroup (S ⊕ (Q × W)) ℂ :=
  queryOp_fwd_unitary (star_mem_unitary hM)

lemma hadamardW_mem_unitary (r m : ℕ) :
    hadamardW r m ∈ Matrix.unitaryGroup (FlagQ r m) ℂ := by
  obtain ⟨hO, hU, _, _, _⟩ :=
    OracleStateHSP.fracOracle_unitary_prepares 1 zero_lt_one le_rfl r m (fun _ => 0)
  have hW_eq : hadamardW r m = star (fracOracle 1 r (fun _ => 0)) * fracU 1 r (fun _ => 0) := by
    rw [fracU, ← mul_assoc, Matrix.mem_unitaryGroup_iff'.mp hO, one_mul]
  rw [hW_eq]
  exact Submonoid.mul_mem _ (star_mem_unitary hO) hU

lemma act_mul {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    act (A * B) v = act A (act B v) := by
  ext i
  simp [act, Matrix.mulVec_mulVec]

lemma act_one {ι : Type*} [Fintype ι] [DecidableEq ι] (v : EuclideanSpace ℂ ι) :
    act (1 : Matrix ι ι ℂ) v = v := by
  simp [act]

noncomputable def simAlgL {Q S W : Type*} [Fintype Q] [Fintype S] [Fintype W]
    [DecidableEq Q] [DecidableEq S] [DecidableEq W] {T : ℕ}
    (A : QueryAlgorithm Q S W T) (M : Matrix Q Q ℂ) (hM : M ∈ Matrix.unitaryGroup Q ℂ)
    (i : Fin T) : Matrix.unitaryGroup (S ⊕ (Q × W)) ℂ :=
  if toDef41Kind (A.kind i) = .inv then ⟨queryOp .inv M, queryOp_inv_unitary hM⟩ else 1

noncomputable def simAlgR {Q S W : Type*} [Fintype Q] [Fintype S] [Fintype W]
    [DecidableEq Q] [DecidableEq S] [DecidableEq W] {T : ℕ}
    (A : QueryAlgorithm Q S W T) (M : Matrix Q Q ℂ) (hM : M ∈ Matrix.unitaryGroup Q ℂ)
    (i : Fin T) : Matrix.unitaryGroup (S ⊕ (Q × W)) ℂ :=
  if toDef41Kind (A.kind i) = .fwd then ⟨queryOp .fwd M, queryOp_fwd_unitary hM⟩ else 1

noncomputable def simAlg {Q S W : Type*} [Fintype Q] [Fintype S] [Fintype W]
    [DecidableEq Q] [DecidableEq S] [DecidableEq W] {T : ℕ}
    (A : QueryAlgorithm Q S W T) (M : Matrix Q Q ℂ) (hM : M ∈ Matrix.unitaryGroup Q ℂ) :
    QueryAlgorithm Q S W T :=
  { U := fun j =>
      let pre : Matrix.unitaryGroup (S ⊕ (Q × W)) ℂ :=
        if h : 0 < (j : ℕ) then simAlgL A M hM ⟨(j : ℕ) - 1, by omega⟩ else 1
      let post : Matrix.unitaryGroup (S ⊕ (Q × W)) ℂ :=
        if h : (j : ℕ) < T then simAlgR A M hM ⟨(j : ℕ), h⟩ else 1
      post * A.U j * pre
    kind := fun i => toDef41Kind (A.kind i) }

lemma simAlg_isDef41 {Q S W : Type*} [Fintype Q] [Fintype S] [Fintype W]
    [DecidableEq Q] [DecidableEq S] [DecidableEq W] {T : ℕ}
    (A : QueryAlgorithm Q S W T) (M : Matrix Q Q ℂ) (hM : M ∈ Matrix.unitaryGroup Q ℂ) :
    (simAlg A M hM).IsDef41 :=
  fun i => toDef41Kind_isFwdOrInv (A.kind i)

lemma stateAt_zero {Q S W : Type*} [Fintype Q] [Fintype S] [Fintype W]
    [DecidableEq Q] [DecidableEq S] [DecidableEq W] {T : ℕ}
    (B : QueryAlgorithm Q S W T) (O : Matrix Q Q ℂ) (ψ : EuclideanSpace ℂ (S ⊕ (Q × W))) :
    B.stateAt O ψ 0 = act (B.U 0 : Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ) ψ := rfl

lemma stateAt_succ {Q S W : Type*} [Fintype Q] [Fintype S] [Fintype W]
    [DecidableEq Q] [DecidableEq S] [DecidableEq W] {T : ℕ}
    (B : QueryAlgorithm Q S W T) (O : Matrix Q Q ℂ) (ψ : EuclideanSpace ℂ (S ⊕ (Q × W)))
    (i : Fin T) :
    B.stateAt O ψ i.succ =
      act (B.U i.succ : Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ)
        (act (queryOp (B.kind i) O) (B.stateAt O ψ i.castSucc)) := rfl

lemma simAlg_finalState {Q S W : Type*} [Fintype Q] [Fintype S] [Fintype W]
    [DecidableEq Q] [DecidableEq S] [DecidableEq W] {T : ℕ}
    (A : QueryAlgorithm Q S W T) (O M : Matrix Q Q ℂ) (hM : M ∈ Matrix.unitaryGroup Q ℂ)
    (hreal : ∀ p q, ((O * M) p q).im = 0)
    (ψ₀ : EuclideanSpace ℂ (S ⊕ (Q × W))) :
    (simAlg A M hM).finalState O ψ₀ = A.finalState (O * M) ψ₀ := by
  have hLR : ∀ i : Fin T,
      (simAlgL A M hM i : Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ) *
          queryOp (toDef41Kind (A.kind i)) O *
          (simAlgR A M hM i : Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ) =
        queryOp (A.kind i) (O * M) := by
    intro i
    have hk_eq : queryOp (S := S) (W := W) (toDef41Kind (A.kind i)) (O * M) =
        queryOp (A.kind i) (O * M) := by
      simp only [queryOp, apply_toDef41Kind_of_real (A.kind i) (O * M) hreal]
    rw [← hk_eq]
    rcases toDef41Kind_isFwdOrInv (A.kind i) with hfwd | hinv
    · have hni : QueryKind.fwd ≠ QueryKind.inv := by decide
      simp only [simAlgL, simAlgR, hfwd, if_neg hni, ↓reduceIte, Submonoid.coe_one, one_mul]
      exact (queryOp_fwd_mul (S := S) (W := W) O M).symm
    · have hnf : QueryKind.inv ≠ QueryKind.fwd := by decide
      simp only [simAlgL, simAlgR, hinv, if_neg hnf, ↓reduceIte, Submonoid.coe_one, mul_one]
      exact (queryOp_inv_mul (S := S) (W := W) O M).symm
  have hstate : ∀ t : Fin (T + 1),
      (simAlg A M hM).stateAt O ψ₀ t =
        act (if h : (t : ℕ) < T then
            (simAlgR A M hM ⟨(t : ℕ), h⟩ : Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ) else 1)
          (A.stateAt (O * M) ψ₀ t) := by
    intro t
    refine Fin.induction ?_ ?_ t
    · rw [stateAt_zero, stateAt_zero]
      have hU0 : (((simAlg A M hM).U 0 : Matrix.unitaryGroup (S ⊕ (Q × W)) ℂ) :
            Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ) =
          (if h : 0 < T then
              (simAlgR A M hM ⟨0, h⟩ : Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ) else 1) *
            (A.U 0 : Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ) := by
        dsimp only [simAlg]
        have hnot : ¬ (0 < ((0 : Fin (T + 1)) : ℕ)) := by simp
        rw [dif_neg hnot, mul_one, Submonoid.coe_mul]
        by_cases h0 : 0 < T
        · have h0' : ((0 : Fin (T + 1)) : ℕ) < T := h0
          have hfin0 : (⟨((0 : Fin (T + 1)) : ℕ), h0'⟩ : Fin T) = ⟨0, h0⟩ := by ext; simp
          rw [dif_pos h0', dif_pos h0, hfin0]
        · have h0' : ¬ (((0 : Fin (T + 1)) : ℕ) < T) := h0
          rw [dif_neg h0', dif_neg h0, Submonoid.coe_one]
      rw [hU0, act_mul]
      rfl
    · intro i ih
      rw [stateAt_succ, stateAt_succ, ih]
      have hiT : (i.castSucc : ℕ) < T := i.isLt
      have hisucc_pos : 0 < (i.succ : ℕ) := Nat.succ_pos _
      have hidx_L : (⟨(i.succ : ℕ) - 1, by omega⟩ : Fin T) = i := by
        ext; simp
      have hidx_R : (⟨(i.castSucc : ℕ), hiT⟩ : Fin T) = i := by
        ext; simp
      rw [dif_pos hiT, hidx_R]
      have hU : (((simAlg A M hM).U i.succ : Matrix.unitaryGroup (S ⊕ (Q × W)) ℂ) :
            Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ) =
          (if h : (i.succ : ℕ) < T then
              (simAlgR A M hM ⟨(i.succ : ℕ), h⟩ : Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ) else 1) *
            (A.U i.succ : Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ) *
            (simAlgL A M hM i : Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ) := by
        simp only [simAlg, hisucc_pos, ↓reduceDIte, hidx_L, Submonoid.coe_mul]
        split_ifs <;> simp
      have hkind : (simAlg A M hM).kind i = toDef41Kind (A.kind i) := rfl
      rw [hU, hkind]
      simp only [← act_mul, mul_assoc]
      congr 2
      have hassoc :
          (simAlgL A M hM i : Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ) *
              (queryOp (toDef41Kind (A.kind i)) O *
                (simAlgR A M hM i : Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ)) =
            (simAlgL A M hM i : Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ) *
              queryOp (toDef41Kind (A.kind i)) O *
              (simAlgR A M hM i : Matrix (S ⊕ (Q × W)) (S ⊕ (Q × W)) ℂ) := by
        rw [mul_assoc]
      rw [hassoc, hLR i]
  unfold QueryAlgorithm.finalState
  rw [hstate (Fin.last T)]
  have hlast : ¬ ((Fin.last T : ℕ) < T) := by simp
  rw [dif_neg hlast, act_one]

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma vm_add_self {m : ℕ} (v : V m) : v + v = 0 := by
  ext i; exact zmod2_add_self (v i)

lemma zsmul_vm_mem {m : ℕ} (s : V m) (k : ℤ) : k • s = 0 ∨ k • s = s := by
  rcases Int.even_or_odd k with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · left
    rw [add_zsmul, ← zsmul_add, vm_add_self, zsmul_zero]
  · right
    have h2 : (2 * t) • s = 0 := by
      rw [mul_comm, mul_zsmul, two_zsmul, vm_add_self, zsmul_zero]
    rw [add_zsmul, h2, one_zsmul, zero_add]

lemma hiddenSubgroup_inj {r m : ℕ} {s₁ s₂ : V m} (hs₁ : s₁ ≠ 0)
    (heq : hiddenSubgroup r s₁ = hiddenSubgroup r s₂) : s₁ = s₂ := by
  have hmem : ((0 : K r), s₁) ∈ hiddenSubgroup r s₁ := by
    simp [hiddenSubgroup, AddSubgroup.mem_prod]
  rw [heq] at hmem
  simp only [hiddenSubgroup, AddSubgroup.mem_prod, AddSubgroup.mem_top, true_and,
    AddSubgroup.mem_zmultiples_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  rcases zsmul_vm_mem s₂ k with h0 | hs
  · rw [h0] at hk
    exact absurd hk.symm hs₁
  · rw [hs] at hk
    exact hk.symm

end AuxThm410

theorem solution :
    ∃ c : ℝ, 0 < c ∧
    ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
    ∀ (n m : ℕ), 1 < m → m ≤ n →
      (∀ x : SimonInst m,
          IsStateHSPInstance (shiftRep (n - m) m) (flagZero (n - m) m) (fracU ε (n - m) x.fn)
            (hiddenSubgroup (n - m) x.period) ε ∧
          Nat.card ((K (n - m) × V m) ⧸ hiddenSubgroup (n - m) x.period) = 2 ^ (m - 1)) ∧
      ∀ (T a b : ℕ) (A : QueryAlgorithm (FlagQ (n - m) m) (Fin a) (Fin b) T)
        (ψ₀ : EuclideanSpace ℂ (Fin a ⊕ (FlagQ (n - m) m × Fin b)))
        (out : Fin a ⊕ (FlagQ (n - m) m × Fin b) → AddSubgroup (K (n - m) × V m)),
        ‖ψ₀‖ = 1 →
        (∀ x : SimonInst m, (2 : ℝ) / 3 ≤
          A.outputProb (fracU ε (n - m) x.fn) ψ₀ out (hiddenSubgroup (n - m) x.period)) →
        c * ((m : ℝ) - 1) / Real.sqrt ε ≤ T := by
  obtain ⟨c, _, hc, _, hQ⟩ := OracleStateHSP.fracOracle_queryComplexity
  refine ⟨c, hc, fun ε hε0 hε1 n m hm1 _hmn => ?_⟩
  set r : ℕ := n - m
  have hm2 : 2 ≤ m := hm1
  refine ⟨fun x => ?_, fun T a b A ψ₀ out hψ₀ hsucc => ?_⟩
  · obtain ⟨_, _, hinst, _, hcardQ⟩ := OracleStateHSP.family_isStateHSP ε hε0 hε1 r m x
    exact ⟨hinst, hcardQ⟩
  · have hW : hadamardW r m ∈ Matrix.unitaryGroup (FlagQ r m) ℂ :=
      AuxThm410.hadamardW_mem_unitary r m
    let A' := AuxThm410.simAlg A (hadamardW r m) hW
    let outP : Fin a ⊕ (FlagQ r m × Fin b) → V m := fun z =>
      open Classical in
      if h : ∃ s : V m, s ≠ 0 ∧ out z = hiddenSubgroup r s then Classical.choose h else 0
    have heval : EvaluatesWithBoundedError A' ψ₀ outP
        (fun x : SimonInst m => fracOracle ε r x.fn) (fun x => x.period) := by
      refine ⟨hψ₀, fun x => ?_⟩
      have hreal : ∀ p q, ((fracOracle ε r x.fn * hadamardW r m) p q).im = 0 :=
        (OracleStateHSP.fracOracle_unitary_prepares ε hε0 hε1 r m x.fn).2.2.2.2
      have hfin : A'.finalState (fracOracle ε r x.fn) ψ₀ =
          A.finalState (fracU ε r x.fn) ψ₀ :=
        AuxThm410.simAlg_finalState A (fracOracle ε r x.fn) (hadamardW r m) hW hreal ψ₀
      refine le_trans (hsucc x) ?_
      rw [QueryAlgorithm.outputProb, QueryAlgorithm.outputProb, hfin]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun z _ _ => sq_nonneg _)
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      have hex : ∃ s : V m, s ≠ 0 ∧ out z = hiddenSubgroup r s := ⟨x.period, x.2.2, hz⟩
      have houtP : outP z = Classical.choose hex := dif_pos hex
      obtain ⟨hs_ne, hs_eq⟩ := Classical.choose_spec hex
      rw [houtP]
      exact AuxThm410.hiddenSubgroup_inj hs_ne (hs_eq.symm.trans hz)
    have hT_mem : (T : ℕ∞) ∈ (fun t : ℕ => (t : ℕ∞)) ''
        {t | ∃ (a' b' : ℕ) (B : QueryAlgorithm (FlagQ r m) (Fin a') (Fin b') t), B.IsDef41 ∧
          ∃ (φ₀ : EuclideanSpace ℂ (Fin a' ⊕ (FlagQ r m × Fin b')))
            (o : Fin a' ⊕ (FlagQ r m × Fin b') → V m),
            EvaluatesWithBoundedError B φ₀ o (fun x : SimonInst m => fracOracle ε r x.fn)
              (fun x => x.period)} :=
      ⟨T, ⟨a, b, A', AuxThm410.simAlg_isDef41 A (hadamardW r m) hW, ψ₀, outP, heval⟩, rfl⟩
    have hqc_le_nat : queryComplexity (fun x : SimonInst m => fracOracle ε r x.fn)
        (fun x => x.period) ≤ (T : ℕ∞) := sInf_le hT_mem
    have hqc_le : (queryComplexity (fun x : SimonInst m => fracOracle ε r x.fn)
        (fun x => x.period) : ℝ≥0∞) ≤ (T : ℝ≥0∞) := by
      exact_mod_cast hqc_le_nat
    have hlow := (hQ ε hε0 hε1 r m hm2).1
    have hle_enn : ENNReal.ofReal (c * ((m : ℝ) - 1) / Real.sqrt ε) ≤
        ENNReal.ofReal (T : ℝ) := by
      rw [ENNReal.ofReal_natCast]
      exact le_trans hlow hqc_le
    exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg T)).mp hle_enn
