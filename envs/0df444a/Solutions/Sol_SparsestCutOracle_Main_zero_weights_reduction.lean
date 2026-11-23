-- Prove2me | solution 1 for SparsestCutOracle.Main.zero_weights_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T12:40:15.388662+00:00
-- url     : https://prove2.me/submissions/4728cb58-9f4d-46aa-9474-f9f471928a0b

import Mathlib
import Definitions.Def_SparsestCutOracle_Main_Guarantees

namespace SparsestCutOracle.Main

open Finset

set_option maxRecDepth 100000

/-! ## General facts about runs -/

theorem step_halted (P : Program) (ω : Tape) (s : State) (h : s.base.halted = true) :
    step P ω s = s := by
  simp [step, h]

theorem run_halted_stable (P : Program) (s : State) (ω : Tape) (t : ℕ)
    (h : (run P s ω t).base.halted = true) : ∀ k, run P s ω (t + k) = run P s ω t := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    show (step P ω)^[t + k + 1] s = _
    rw [Function.iterate_succ_apply']
    change step P ω (run P s ω (t + k)) = _
    rw [ih, step_halted _ _ _ h]

theorem final_eq_of_halted (P : Program) (s : State) (ω : Tape) (t : ℕ)
    (h : (run P s ω t).base.halted = true) : final P s ω = run P s ω t := by
  classical
  have hH : Halts P s ω := ⟨t, h⟩
  have hle : haltTime P s ω ≤ t := by
    unfold haltTime; rw [dif_pos hH]; exact Nat.find_min' hH h
  have hspec : (run P s ω (haltTime P s ω)).base.halted = true := by
    unfold haltTime; rw [dif_pos hH]; exact Nat.find_spec hH
  unfold final
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  rw [hk, run_halted_stable P s ω _ hspec k]

theorem final_halted (P : Program) (s : State) (ω : Tape) (h : Halts P s ω) :
    (final P s ω).base.halted = true := by
  classical
  unfold final haltTime; rw [dif_pos h]; exact Nat.find_spec h

theorem work_of_halts (P : Program) (s : State) (ω : Tape) (h : Halts P s ω) :
    work P s ω = ((final P s ω).base.work : ℝ) := by
  unfold work; simp [h]

/-! ## The perturbation and the post-processing -/

/-- Output post-processing: empty if `π(S) ≤ 0`, `S` if `π(S) ≤ π(Sᶜ)`, else `Sᶜ`. -/
noncomputable def postOut {n : ℕ} (π : Fin n → ℝ) (S : Finset (Fin n)) : Finset (Fin n) :=
  if mass π S ≤ 0 then ∅ else if mass π S - mass π Sᶜ ≤ 0 then S else Sᶜ

/-- Scale factor: `A n^6` if some weight vanishes, `1` otherwise (as computed branch-free). -/
noncomputable def pertN {n : ℕ} (A : ℕ) (π : Fin n → ℝ) : ℝ :=
  (A : ℝ) * (n : ℝ) ^ 6 + (∏ v, π v / π v) * (1 - (A : ℝ) * (n : ℝ) ^ 6)

/-- Perturbed weights: zero weights become `1`, positive weights are multiplied by `N`. -/
noncomputable def pertW {n : ℕ} (N : ℝ) (π : Fin n → ℝ) : Fin n → ℝ :=
  fun v => N * π v + (1 - π v / π v)

/-! ## Mass and cut facts -/

theorem mass_nonneg {n : ℕ} {π : Fin n → ℝ} (h : ∀ v, 0 ≤ π v) (S : Finset (Fin n)) :
    0 ≤ mass π S :=
  Finset.sum_nonneg (fun v _ => h v)

theorem mass_add_compl {n : ℕ} (π : Fin n → ℝ) (S : Finset (Fin n)) :
    mass π S + mass π Sᶜ = totalWeight π := by
  unfold totalWeight mass; exact Finset.sum_add_sum_compl S π

theorem postOut_balanced {n : ℕ} (π : Fin n → ℝ) (h : ∀ v, 0 ≤ π v) (S : Finset (Fin n)) :
    mass π (postOut π S) ≤ mass π (postOut π S)ᶜ := by
  unfold postOut
  split_ifs with h1 h2
  · rw [show mass π ∅ = 0 from Finset.sum_empty]; exact mass_nonneg h _
  · linarith
  · rw [compl_compl]; linarith

theorem mass_pert {n : ℕ} (N : ℝ) (π : Fin n → ℝ) (X : Finset (Fin n)) :
    mass (pertW N π) X = N * mass π X + ((X.filter (fun v => π v = 0)).card : ℝ) := by
  unfold mass pertW
  rw [Finset.mul_sum, Finset.card_filter, Nat.cast_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  by_cases hv : π v = 0
  · simp [hv]
  · simp [hv]

theorem mass_ge_one {n : ℕ} {π : Fin n → ℝ} (h0 : ∀ v, 0 ≤ π v) (h1 : ∀ v, 0 < π v → 1 ≤ π v)
    (S : Finset (Fin n)) (hS : 0 < mass π S) : 1 ≤ mass π S := by
  obtain ⟨v, hv, hpos⟩ : ∃ v ∈ S, 0 < π v := by
    by_contra hc
    push Not at hc
    have : mass π S ≤ 0 := Finset.sum_nonpos (fun v hv => hc v hv)
    linarith
  calc 1 ≤ π v := h1 v hpos
    _ ≤ mass π S := Finset.single_le_sum (fun w _ => h0 w) hv

theorem cut_comm {n : ℕ} (G : ClusterDecomp.WGraph (Fin n)) (S T : Finset (Fin n)) :
    cut G S T = cut G T S := by
  unfold cut ClusterDecomp.WGraph.cut ClusterDecomp.cutCap
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => G.symm _ _))

theorem cut_mono {n : ℕ} (G : ClusterDecomp.WGraph (Fin n)) {S S' T T' : Finset (Fin n)}
    (hS : S ⊆ S') (hT : T ⊆ T') : cut G S T ≤ cut G S' T' := by
  unfold cut ClusterDecomp.WGraph.cut ClusterDecomp.cutCap
  calc ∑ u ∈ S, ∑ v ∈ T, G.w u v ≤ ∑ u ∈ S, ∑ v ∈ T', G.w u v :=
        Finset.sum_le_sum (fun u _ =>
          Finset.sum_le_sum_of_subset_of_nonneg hT (fun v _ _ => G.nonneg _ _))
    _ ≤ ∑ u ∈ S', ∑ v ∈ T', G.w u v :=
        Finset.sum_le_sum_of_subset_of_nonneg hS
          (fun u _ _ => Finset.sum_nonneg (fun v _ => G.nonneg _ _))

theorem expanding_transfer {n : ℕ} (G : ClusterDecomp.WGraph (Fin n)) (π π' : Fin n → ℝ)
    (U : Finset (Fin n)) (ϕ N : ℝ) (hϕ : 0 < ϕ) (hN : 0 < N)
    (hle : ∀ X, N * mass π X ≤ mass π' X)
    (h : ExpandingOn G π' U (ϕ / N)) : ExpandingOn G π U ϕ := by
  intro X hXU hX
  have key : ∀ Y, ϕ * mass π Y ≤ ϕ / N * mass π' Y := by
    intro Y
    have := hle Y
    rw [div_mul_eq_mul_div, le_div_iff₀ hN]
    nlinarith
  by_cases hc : mass π' X ≤ mass π' (U \ X)
  · exact le_trans (key X) (h X hXU hc)
  · push Not at hc
    have hUY : U \ (U \ X) = X := Finset.sdiff_sdiff_eq_self hXU
    have h2 := h (U \ X) Finset.sdiff_subset (by rw [hUY]; exact hc.le)
    rw [hUY] at h2
    calc ϕ * mass π X ≤ ϕ * mass π (U \ X) := mul_le_mul_of_nonneg_left hX hϕ.le
      _ ≤ ϕ / N * mass π' (U \ X) := key _
      _ ≤ cut G (U \ X) X := h2
      _ = cut G X (U \ X) := cut_comm G _ _

theorem expanding_extend {n : ℕ} (G : ClusterDecomp.WGraph (Fin n)) (π : Fin n → ℝ)
    (U V : Finset (Fin n)) (hUV : U ⊆ V) (h0 : ∀ v ∈ V \ U, π v = 0) (ϕ : ℝ)
    (h : ExpandingOn G π U ϕ) : ExpandingOn G π V ϕ := by
  intro X hXV hX
  have e1 : mass π (X ∩ U) = mass π X := by
    unfold mass
    apply Finset.sum_subset Finset.inter_subset_left
    intro v hvX hvn
    apply h0
    simp only [Finset.mem_sdiff, Finset.mem_inter] at *
    exact ⟨hXV hvX, fun hu => hvn ⟨hvX, hu⟩⟩
  have hsub : U \ (X ∩ U) ⊆ V \ X := by
    intro v hv
    simp only [Finset.mem_sdiff, Finset.mem_inter] at *
    exact ⟨hUV hv.1, fun hx => hv.2 ⟨hx, hv.1⟩⟩
  have e2 : mass π (U \ (X ∩ U)) = mass π (V \ X) := by
    unfold mass
    apply Finset.sum_subset hsub
    intro v hv hvn
    apply h0
    simp only [Finset.mem_sdiff, Finset.mem_inter] at *
    tauto
  have h1 := h (X ∩ U) Finset.inter_subset_right (by rw [e1, e2]; exact hX)
  rw [e1] at h1
  exact le_trans h1 (cut_mono _ Finset.inter_subset_left hsub)

theorem log_bounds {n : ℕ} (hn : 2 ≤ n) :
    0 < Real.log n ∧ (1:ℝ) / 2 ≤ Real.log n ∧ (1:ℝ) / 32 ≤ Real.log n ^ 5 := by
  have hlog2 : (1:ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlogn : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  refine ⟨by linarith, by linarith, ?_⟩
  have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1 / 2) (by linarith : (1:ℝ) / 2 ≤ Real.log n) 5
  norm_num at this ⊢
  linarith

/-- The cut guarantee transfers from the perturbed instance to the original one. -/
theorem goodcut_transfer {n : ℕ} (hn : 2 ≤ n) (G : Graph n) (π : Fin n → ℝ) (ϕ κ cβ Cq N : ℝ)
    (hϕ : 0 < ϕ) (hβ : 0 < cβ) (hq : 0 < Cq) (hN : 0 < N)
    (h0 : ∀ v, 0 ≤ π v) (h1 : ∀ v, 0 < π v → 1 ≤ π v) (hT : 1 ≤ totalWeight π)
    (hZ1 : ((univ.filter (fun v => π v = 0)).card : ℝ) < N)
    (hZ2 : ((univ.filter (fun v => π v = 0)).card : ℝ) ≤ cβ / 2 * N / Real.log n ^ 5)
    (S : Finset (Fin n)) (hbal : mass (pertW N π) S ≤ mass (pertW N π) Sᶜ)
    (hg : GoodCut G (pertW N π) (ϕ / N) κ cβ Cq S) :
    GoodCut G π ϕ κ (min (cβ / 2) (1 / 200)) (4 * Cq) (postOut π S) := by
  obtain ⟨hlogpos, -, hL32⟩ := log_bounds hn
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log n ^ 5 := ⟨_, rfl⟩
  rw [← hLdef] at hZ2 hL32
  have hLpos : 0 < L := by linarith
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = ((univ.filter (fun v => π v = 0)).card : ℝ) := ⟨_, rfl⟩
  rw [← hz] at hZ1 hZ2
  have hcardX : ∀ X : Finset (Fin n), ((X.filter (fun v => π v = 0)).card : ℝ) ≤ z := by
    intro X; rw [hz]; exact_mod_cast Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.subset_univ X))
  have hle : ∀ X, N * mass π X ≤ mass (pertW N π) X := by
    intro X; rw [mass_pert]; have := Nat.cast_nonneg (α := ℝ) (X.filter (fun v => π v = 0)).card
    linarith
  have hub : ∀ X, mass (pertW N π) X ≤ N * mass π X + z := by
    intro X; rw [mass_pert]; linarith [hcardX X]
  have htot : N * totalWeight π ≤ totalWeight (pertW N π) := hle univ
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = Real.sqrt (Real.log n / κ) := ⟨_, rfl⟩
  have hQ : 0 ≤ Q := by rw [hQdef]; exact Real.sqrt_nonneg _
  obtain ⟨K, hKdef⟩ : ∃ K, K = Cq * ϕ * Q := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [hKdef]; positivity
  have hzN : z / N < 1 := (div_lt_one hN).2 hZ1
  have hz0 : 0 ≤ z := by rw [hz]; exact Nat.cast_nonneg _
  have hcut : cut G.toWGraph S Sᶜ ≤ K * mass π S + K * (z / N) := by
    have e : Cq * (ϕ / N) * Real.sqrt (Real.log n / κ) * mass (pertW N π) S =
        K * mass (pertW N π) S / N := by rw [hKdef, hQdef]; ring
    have h2 : K * mass (pertW N π) S / N ≤ K * mass π S + K * (z / N) := by
      rw [div_le_iff₀ hN]
      calc K * mass (pertW N π) S ≤ K * (N * mass π S + z) := mul_le_mul_of_nonneg_left (hub S) hK
        _ = (K * mass π S + K * (z / N)) * N := by
          rw [add_mul, mul_assoc K (z / N) N, div_mul_cancel₀ z hN.ne']; ring
    linarith [hg.1, e]
  obtain ⟨c, hcdef⟩ : ∃ c, c = cβ / L := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  have hZc : z ≤ c * N / 2 := by rw [hcdef]; rw [show cβ / L * N / 2 = cβ / 2 * N / L by ring]; exact hZ2
  have hcN : c * N ≤ c * totalWeight (pertW N π) := by
    calc c * N ≤ c * (N * totalWeight π) :=
          mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hN.le hT) hc.le
      _ ≤ c * totalWeight (pertW N π) := mul_le_mul_of_nonneg_left htot hc.le
  have hcN' : c * N * totalWeight π ≤ c * totalWeight (pertW N π) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left htot hc.le
  have hsum := mass_add_compl π S
  have hb0 := mass_nonneg h0 Sᶜ
  have hexp : mass (pertW N π) S < c * totalWeight (pertW N π) →
      ExpandingOn G.toWGraph π Sᶜ ϕ := by
    intro hs
    have := hg.2 (by rw [← hLdef, ← hcdef]; exact hs)
    exact expanding_transfer _ π _ _ ϕ N hϕ hN hle this
  have hmin1 : min (cβ / 2) (1 / 200) ≤ cβ / 2 := min_le_left _ _
  have hmin2 : min (cβ / 2) (1 / 200) ≤ 1 / 200 := min_le_right _ _
  unfold postOut
  split_ifs with ha hab
  · -- empty output
    have hS0 : ∀ v ∈ S, π v = 0 := by
      have hm0 : mass π S = 0 := le_antisymm ha (mass_nonneg h0 S)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => h0 v)).1 hm0
    constructor
    · simp [cut, ClusterDecomp.WGraph.cut, ClusterDecomp.cutCap, mass]
    · intro _
      have hNa : N * mass π S ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN.le ha
      have hs : mass (pertW N π) S < c * totalWeight (pertW N π) := by
        have := hub S
        have : 0 < c * N := mul_pos hc hN
        linarith
      refine expanding_extend _ π Sᶜ _ (by simp) ?_ ϕ (hexp hs)
      intro v hv
      simp only [Finset.mem_sdiff, Finset.mem_compl, not_not] at hv
      exact hS0 v hv.2
  · -- output S
    push Not at ha
    have ha1 := mass_ge_one h0 h1 S ha
    constructor
    · rw [show 4 * Cq * ϕ * Real.sqrt (Real.log n / κ) * mass π S = 4 * K * mass π S by
        rw [hKdef, hQdef]; ring]
      have : K * (z / N) ≤ K := by nlinarith
      nlinarith
    · intro hsmall
      apply hexp
      have h3 : min (cβ / 2) (1 / 200) / Real.log n ^ 5 * totalWeight π ≤ c / 2 * totalWeight π := by
        rw [← hLdef, hcdef]
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        rw [show cβ / L / 2 = cβ / 2 / L by ring]
        exact div_le_div_of_nonneg_right hmin1 hLpos.le
      have h4 : N * mass π S < N * (c / 2 * totalWeight π) := mul_lt_mul_of_pos_left (by linarith) hN
      have := hub S
      nlinarith
  · -- output the complement
    push Not at ha hab
    have ha1 := mass_ge_one h0 h1 S ha
    have hNab : N * (mass π S - mass π Sᶜ) ≤ z := by
      have := hle S; have := hub Sᶜ; rw [mul_sub]; linarith
    have hab' : mass π S - mass π Sᶜ ≤ z / N := by rw [le_div_iff₀ hN]; linarith
    have hbpos : 0 < mass π Sᶜ := by linarith
    have hb1 := mass_ge_one h0 h1 Sᶜ hbpos
    constructor
    · rw [compl_compl, cut_comm,
        show 4 * Cq * ϕ * Real.sqrt (Real.log n / κ) * mass π Sᶜ = 4 * K * mass π Sᶜ by
          rw [hKdef, hQdef]; ring]
      have : K * (z / N) ≤ K := by nlinarith
      have h5 : K * mass π S ≤ K * (2 * mass π Sᶜ) := mul_le_mul_of_nonneg_left (by linarith) hK
      have h6 : K ≤ K * mass π Sᶜ := le_mul_of_one_le_right hK hb1
      linarith
    · intro hsmall
      exfalso
      have h3 : min (cβ / 2) (1 / 200) / Real.log n ^ 5 ≤ 32 / 200 := by
        rw [← hLdef, div_le_iff₀ hLpos]; linarith
      have h4 : mass π Sᶜ < 32 / 200 * totalWeight π := by
        have := mul_le_mul_of_nonneg_right h3 (by linarith : (0:ℝ) ≤ totalWeight π)
        linarith
      linarith

theorem total_zero_or_ge_one {n : ℕ} (G : Graph n) (h : G.UnitLowerBound) :
    G.total = 0 ∨ 1 ≤ G.total := by
  unfold Graph.total
  cases G with
  | nil => left; simp
  | cons e G' =>
    right
    simp only [List.map_cons, List.sum_cons]
    have h1 : 1 ≤ (e.capacity : ℝ) := h e (by simp)
    have h2 : 0 ≤ (G'.map fun e => (e.capacity : ℝ)).sum := List.sum_nonneg (by simp)
    linarith

theorem pert_props {n : ℕ} (hn : 2 ≤ n) (π : Fin n → ℝ) (hπ : NormalizedWeights π) (d A : ℕ)
    (cβ : ℝ) (hβ : 0 < cβ) (hA : 2 / cβ ≤ A) (hA1 : 1 ≤ A) (hd : totalWeight π ≤ (n : ℝ) ^ d) :
    0 < pertN A π ∧ ((univ.filter (fun v => π v = 0)).card : ℝ) < pertN A π ∧
      ((univ.filter (fun v => π v = 0)).card : ℝ) ≤ cβ / 2 * pertN A π / Real.log n ^ 5 ∧
      NormalizedWeights (pertW (pertN A π) π) ∧ (∀ v, 0 < pertW (pertN A π) π v) ∧
      totalWeight (pertW (pertN A π) π) ≤ (n : ℝ) ^ (d + 6 + A) := by
  obtain ⟨hlogpos, -, -⟩ := log_bounds hn
  have hx : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hx1 : (1:ℝ) ≤ n := by linarith
  have hT1 : 1 ≤ totalWeight π := by
    obtain ⟨v, hv⟩ := hπ.2.1
    rw [← hv]; exact Finset.single_le_sum (fun w _ => hπ.1 w) (Finset.mem_univ v)
  have hpowd : (n : ℝ) ^ d ≤ (n : ℝ) ^ (d + 6 + A) := pow_le_pow_right₀ hx1 (by omega)
  by_cases hz : ∃ v, π v = 0
  · obtain ⟨v0, hv0⟩ := hz
    have hprod : (∏ v, π v / π v) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v0) (by rw [hv0]; simp)
    have hN : pertN A π = (A : ℝ) * (n : ℝ) ^ 6 := by unfold pertN; rw [hprod]; ring
    have hAr : (1:ℝ) ≤ A := by exact_mod_cast hA1
    have h6 : (n : ℝ) < (n : ℝ) ^ 6 := by
      have h5 : (1:ℝ) < (n : ℝ) ^ 5 := one_lt_pow₀ (by linarith) (by norm_num)
      calc (n : ℝ) = n * 1 := by ring
        _ < n * n ^ 5 := mul_lt_mul_of_pos_left h5 (by linarith)
        _ = n ^ 6 := by ring
    have hzn : ((univ.filter (fun v => π v = 0)).card : ℝ) ≤ n := by
      have := Finset.card_le_univ (univ.filter (fun v => π v = 0))
      simp only [Fintype.card_fin] at this
      exact_mod_cast this
    have hN1 : (1:ℝ) ≤ pertN A π := by rw [hN]; nlinarith
    have hNpos : 0 < pertN A π := by linarith
    have hW : ∀ v, pertW (pertN A π) π v = if π v = 0 then 1 else pertN A π * π v := by
      intro v; unfold pertW; by_cases hv : π v = 0
      · simp [hv]
      · simp [hv]
    have hpos : ∀ v, 0 < π v → 1 ≤ pertW (pertN A π) π v := by
      intro v hv; rw [hW, if_neg hv.ne']; nlinarith [hπ.2.2 v hv]
    refine ⟨hNpos, ?_, ?_, ⟨?_, ⟨v0, by rw [hW, if_pos hv0]⟩, ?_⟩, ?_, ?_⟩
    · rw [hN]; nlinarith
    · have hLn : Real.log n ^ 5 ≤ (n : ℝ) ^ 5 :=
        pow_le_pow_left₀ hlogpos.le (Real.log_le_self (by linarith)) 5
      have hLpos : 0 < Real.log n ^ 5 := by positivity
      rw [le_div_iff₀ hLpos, hN]
      have hcA : 1 ≤ cβ / 2 * A := by
        rw [div_le_iff₀ hβ] at hA; nlinarith
      calc ((univ.filter (fun v => π v = 0)).card : ℝ) * Real.log n ^ 5 ≤ n * n ^ 5 :=
            mul_le_mul hzn hLn (by positivity) (by linarith)
        _ = 1 * n ^ 6 := by ring
        _ ≤ cβ / 2 * A * n ^ 6 := mul_le_mul_of_nonneg_right hcA (by positivity)
        _ = cβ / 2 * (A * n ^ 6) := by ring
    · intro v; rw [hW]; split_ifs
      · norm_num
      · exact mul_nonneg hNpos.le (hπ.1 v)
    · intro v _; by_cases hv : π v = 0
      · rw [hW, if_pos hv]
      · exact hpos v (lt_of_le_of_ne (hπ.1 v) (Ne.symm hv))
    · intro v; by_cases hv : π v = 0
      · rw [hW, if_pos hv]; norm_num
      · linarith [hpos v (lt_of_le_of_ne (hπ.1 v) (Ne.symm hv))]
    · unfold totalWeight; rw [mass_pert, hN]
      change (A : ℝ) * n ^ 6 * totalWeight π + _ ≤ _
      have h2A : ((A + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ A := by
        have h1 : A + 1 ≤ 2 ^ A := A.lt_two_pow_self
        calc ((A + 1 : ℕ) : ℝ) ≤ ((2 ^ A : ℕ) : ℝ) := by exact_mod_cast h1
          _ = (2 : ℝ) ^ A := by push_cast; ring
          _ ≤ (n : ℝ) ^ A := pow_le_pow_left₀ (by norm_num) hx A
      push_cast at h2A
      have hn6 : (n : ℝ) ≤ (n : ℝ) ^ (d + 6) := le_self_pow₀ hx1 (by omega)
      have hp : (n : ℝ) ^ (d + 6 + A) = (n : ℝ) ^ 6 * (n : ℝ) ^ d * (n : ℝ) ^ A := by ring
      have hp2 : (n : ℝ) ^ (d + 6) = (n : ℝ) ^ 6 * (n : ℝ) ^ d := by ring
      rw [hp]
      have hq6 : 0 ≤ (n : ℝ) ^ 6 := by positivity
      have hqd : 0 ≤ (n : ℝ) ^ d := by positivity
      have e1 : (A : ℝ) * n ^ 6 * totalWeight π ≤ A * (n ^ 6 * n ^ d) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hq6) (by linarith)
      have e2 : (A + 1 : ℝ) * (n ^ 6 * n ^ d) ≤ n ^ A * (n ^ 6 * n ^ d) :=
        mul_le_mul_of_nonneg_right h2A (by positivity)
      nlinarith
  · push Not at hz
    have hprod : (∏ v, π v / π v) = 1 := Finset.prod_eq_one (fun v _ => div_self (hz v))
    have hN : pertN A π = 1 := by unfold pertN; rw [hprod]; ring
    have hW : pertW (pertN A π) π = π := by
      funext v; unfold pertW; rw [hN, div_self (hz v)]; ring
    have hcard : (univ.filter (fun v => π v = 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro v _; exact hz v
    rw [hW, hN, hcard]
    refine ⟨by norm_num, by norm_num, ?_, hπ, ?_, le_trans hd hpowd⟩
    · have : 0 < Real.log n ^ 5 := by positivity
      simp only [Nat.cast_zero]; positivity
    · intro v; exact lt_of_le_of_ne (hπ.1 v) (Ne.symm (hz v))

/-! ## The machine construction -/

/-- A base instruction. -/
abbrev iB (i : ClusterDecomp.Instr) : Instr := .base i
/-- A core instruction. -/
abbrev iC (i : SmaleNinth.RAMInstr) : Instr := .base (.core i)

/-- An upper bound for the pointer indices mentioned by an instruction. -/
def ptrIdx : Instr → ℕ
  | .base (.core (.load _ q)) => q
  | .base (.core (.store q _)) => q
  | .base (.core (.pset q _)) => q
  | .base (.core (.pcopy q q')) => q + q'
  | .base (.core (.pinc q)) => q
  | .base (.core (.pdec q)) => q
  | .base (.core (.pjle q q' _)) => q + q'
  | .base (.pointerAdd d a b) => d + a + b
  | .base (.pointerSub d a b) => d + a + b
  | .base (.integerLoad d a) => d + a
  | .base (.integerStore a b) => a + b
  | .base (.pointerReal _ a) => a
  | _ => 0

/-- A pointer register not used by `P`. -/
def scratch (P : Program) : ℕ := (P.map ptrIdx).sum + 1

/-- Relocation of one instruction: real-memory cell `z` of `P` lives at cell `2z`, jump targets
`t` go to `off + 2t`, and `halt` jumps to the post-processing code. Every image has length 2. -/
def transInstr (T off post : ℕ) : Instr → List Instr
  | .base (.core (.load d q)) => [iB (.pointerAdd T q q), iC (.load d T)]
  | .base (.core (.store q i)) => [iB (.pointerAdd T q q), iC (.store T i)]
  | .base (.core (.jle i t)) => [iC (.pset T 0), iC (.jle i (off + 2 * t))]
  | .base (.core (.pjle q q' t)) => [iC (.pset T 0), iC (.pjle q q' (off + 2 * t))]
  | .base .halt => [iC (.pjle T T post), iC (.pset T 0)]
  | i => [i, iC (.pset T 0)]

def preCode (A : ℕ) (off : ℕ) : List Instr := [
  iC (.pset 1 (-1)),
  iC (.pset 2 1),
  iB (.integerLoad 3 0),
  iB (.integerLoad 4 2),
  iB (.pointerAdd 5 4 3),
  iC (.pinc 5),
  iC (.pjle 5 1 12),
  iB (.pointerAdd 6 5 5),
  iC (.load 0 5),
  iC (.store 6 0),
  iC (.pdec 5),
  iC (.pjle 0 0 6),
  iB (.pointerReal 7 3),
  iC (.const 8 (A : ℝ)),
  iC (.mul 1 8 7),
  iC (.mul 1 1 7),
  iC (.mul 1 1 7),
  iC (.mul 1 1 7),
  iC (.mul 1 1 7),
  iC (.mul 1 1 7),
  iC (.const 6 1),
  iC (.const 2 1),
  iB (.pointerAdd 5 4 4),
  iC (.pcopy 7 3),
  iC (.pjle 7 0 32),
  iC (.load 0 5),
  iC (.div 3 0 0),
  iC (.mul 2 2 3),
  iC (.pinc 5),
  iC (.pinc 5),
  iC (.pdec 7),
  iC (.pjle 0 0 24),
  iC (.sub 3 6 1),
  iC (.mul 3 2 3),
  iC (.add 1 1 3),
  iB (.pointerAdd 5 4 4),
  iC (.pset 8 1),
  iC (.pcopy 7 3),
  iC (.pjle 7 0 52),
  iC (.load 0 5),
  iC (.store 8 0),
  iC (.mul 3 1 0),
  iC (.div 2 0 0),
  iC (.sub 2 6 2),
  iC (.add 3 3 2),
  iC (.store 5 3),
  iC (.pinc 5),
  iC (.pinc 5),
  iC (.pinc 8),
  iC (.pinc 8),
  iC (.pdec 7),
  iC (.pjle 0 0 38),
  iC (.load 0 5),
  iC (.div 0 0 1),
  iC (.store 5 0),
  iC (.store 1 7),
  iC (.pset 1 0),
  iC (.pset 2 0),
  iC (.pset 3 0),
  iC (.pset 4 0),
  iC (.pset 5 0),
  iC (.pset 6 0),
  iC (.pset 7 0),
  iC (.pset 8 0),
  iC (.const 0 0),
  iC (.const 1 0),
  iC (.const 2 0),
  iC (.const 3 0),
  iC (.const 6 0),
  iC (.const 7 0),
  iC (.const 8 0),
  iC (.pjle 0 0 off)]

def postCode : List Instr := [
  iC (.pset 0 0),
  iC (.pset 1 (-1)),
  iC (.pset 8 1),
  iC (.pset 9 (-1)),
  iC (.load 11 1),
  iC (.const 6 1),
  iC (.const 9 0),
  iC (.const 10 0),
  iC (.jle 11 95),
  iB (.integerLoad 10 9),
  iB (.pointerReal 0 10),
  iC (.div 0 0 0),
  iC (.load 3 8),
  iC (.mul 4 3 0),
  iC (.add 9 9 4),
  iC (.sub 0 6 0),
  iC (.mul 4 3 0),
  iC (.add 10 10 4),
  iC (.pdec 9),
  iC (.pinc 8),
  iC (.pinc 8),
  iC (.sub 11 11 6),
  iC (.pjle 0 0 80),
  iC (.sub 0 9 10),
  iC (.jle 9 104),
  iC (.jle 0 101),
  iC (.pset 11 0),
  iC (.pset 12 1),
  iC (.pjle 0 0 108),
  iC (.pset 11 1),
  iC (.pset 12 0),
  iC (.pjle 0 0 108),
  iC (.pset 11 0),
  iC (.pset 12 0),
  iC (.pset 10 0),
  iC (.pset 10 0),
  iC (.pset 9 (-1)),
  iC (.load 11 1),
  iC (.jle 11 125),
  iB (.integerLoad 13 9),
  iC (.pjle 13 0 116),
  iC (.pcopy 14 11),
  iC (.pset 10 0),
  iC (.pjle 0 0 121),
  iC (.pjle 0 13 119),
  iC (.pcopy 14 11),
  iC (.pjle 0 0 121),
  iC (.pcopy 14 12),
  iC (.pset 10 0),
  iB (.integerStore 9 14),
  iC (.pdec 9),
  iC (.sub 11 11 6),
  iC (.pjle 0 0 110),
  iB (.halt)]


/-- Start of the relocated copy of `P`. -/
def offs : ℕ := 126
/-- Start of the post-processing code. -/
def postStart : ℕ := 72

/-- The reduction program: prologue, post-processing, relocated `P`. -/
def fullProg (A : ℕ) (P : Program) : Program :=
  preCode A offs ++ postCode ++ P.flatMap (transInstr (scratch P) offs postStart)

/-- Number of prologue steps. -/
def preWork (n m : ℕ) : ℕ := 6 * (m + n + 2) + 22 * n + 47
/-- Number of post-processing steps (including the final `halt`). -/
def postWork (n : ℕ) : ℕ := 25 * n + 19

/-- `s'` (a state of `fullProg`) simulates `s` (a state of `P`). -/
structure Sim (T off : ℕ) (D : ℤ → ℝ) (K : ℕ) (s s' : State) : Prop where
  pc : s'.base.core.pc = off + 2 * s.base.core.pc
  regs : s'.base.core.regs = s.base.core.regs
  ptrs : ∀ q, q ≠ T → s'.base.core.ptrs q = s.base.core.ptrs q
  memE : ∀ z : ℤ, s'.base.core.mem (2 * z) = s.base.core.mem z
  memO : ∀ z : ℤ, s'.base.core.mem (2 * z + 1) = D z
  imem : s'.base.integerMemory = s.base.integerMemory
  cursor : s'.base.cursor = s.base.cursor
  gcur : s'.gaussianCursor = s.gaussianCursor
  halted' : s'.base.halted = false
  halted : s.base.halted = false
  work : s'.base.work = K + 2 * s.base.work

theorem run_add (P : Program) (s : State) (ω : Tape) (a b : ℕ) :
    run P s ω (a + b) = run P (run P s ω a) ω b := by
  unfold run; rw [add_comm, Function.iterate_add_apply]

theorem run_succ (P : Program) (s : State) (ω : Tape) (k : ℕ) :
    run P s ω (k + 1) = step P ω (run P s ω k) := by
  unfold run; rw [Function.iterate_succ_apply']

theorem not_halted_of_succ (P : Program) (s : State) (ω : Tape) (k : ℕ)
    (h : (run P s ω (k + 1)).base.halted = false) : (run P s ω k).base.halted = false := by
  cases hk : (run P s ω k).base.halted
  · rfl
  · have := run_halted_stable P s ω k hk 1
    rw [this, hk] at h; cases h

theorem outputCut_congr (n : ℕ) (s t : State)
    (h : s.base.integerMemory = t.base.integerMemory) : outputCut n s = outputCut n t := by
  unfold outputCut ClusterDecomp.label; rw [h]

/-! ## Single-instruction semantics -/

noncomputable def coreExec (ci : SmaleNinth.RAMInstr) (s : SmaleNinth.RAMConfig) :
    SmaleNinth.RAMConfig :=
  match ci with
  | .const dst c => ⟨s.pc + 1, Function.update s.regs dst c, s.ptrs, s.mem⟩
  | .add dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i + s.regs j), s.ptrs, s.mem⟩
  | .sub dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i - s.regs j), s.ptrs, s.mem⟩
  | .mul dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i * s.regs j), s.ptrs, s.mem⟩
  | .div dst i j => ⟨s.pc + 1, Function.update s.regs dst (s.regs i / s.regs j), s.ptrs, s.mem⟩
  | .load dst q => ⟨s.pc + 1, Function.update s.regs dst (s.mem (s.ptrs q)), s.ptrs, s.mem⟩
  | .store q i => ⟨s.pc + 1, s.regs, s.ptrs, Function.update s.mem (s.ptrs q) (s.regs i)⟩
  | .pset q c => ⟨s.pc + 1, s.regs, Function.update s.ptrs q c, s.mem⟩
  | .pcopy q q' => ⟨s.pc + 1, s.regs, Function.update s.ptrs q (s.ptrs q'), s.mem⟩
  | .pinc q => ⟨s.pc + 1, s.regs, Function.update s.ptrs q (s.ptrs q + 1), s.mem⟩
  | .pdec q => ⟨s.pc + 1, s.regs, Function.update s.ptrs q (s.ptrs q - 1), s.mem⟩
  | .jle i target => if s.regs i ≤ 0 then ⟨target, s.regs, s.ptrs, s.mem⟩ else
      ⟨s.pc + 1, s.regs, s.ptrs, s.mem⟩
  | .pjle q q' target => if s.ptrs q ≤ s.ptrs q' then ⟨target, s.regs, s.ptrs, s.mem⟩ else
      ⟨s.pc + 1, s.regs, s.ptrs, s.mem⟩
  | .accept => s
  | .reject => s

theorem coreExec_eq (R : SmaleNinth.RAMProgram) (c : SmaleNinth.RAMConfig)
    (ci : SmaleNinth.RAMInstr) (h : R[c.pc]? = some ci) : SmaleNinth.RAMStep R c = coreExec ci c := by
  unfold SmaleNinth.RAMStep; rw [h]; cases ci <;> rfl

noncomputable def bexec (ω : ℕ → Bool) (i : ClusterDecomp.Instr) (s : ClusterDecomp.State) :
    ClusterDecomp.State :=
  let t : ClusterDecomp.State := { s with
      work := s.work + 1
      core := { s.core with pc := s.core.pc + 1 } }
  match i with
  | .core ci => { t with core := coreExec ci s.core }
  | .pointerAdd d a b =>
      { t with core := { t.core with
          ptrs := Function.update s.core.ptrs d (s.core.ptrs a + s.core.ptrs b) } }
  | .pointerSub d a b =>
      { t with core := { t.core with
          ptrs := Function.update s.core.ptrs d (s.core.ptrs a - s.core.ptrs b) } }
  | .integerLoad d a =>
      { t with core := { t.core with
          ptrs := Function.update s.core.ptrs d (s.integerMemory (s.core.ptrs a)) } }
  | .integerStore a b =>
      { t with integerMemory := Function.update s.integerMemory (s.core.ptrs a) (s.core.ptrs b) }
  | .pointerReal d a =>
      { t with core := { t.core with
          regs := Function.update s.core.regs d (s.core.ptrs a : ℝ) } }
  | .coin d =>
      { t with
        cursor := s.cursor + 1
        core := { t.core with
          regs := Function.update s.core.regs d (if ω s.cursor then 1 else 0) } }
  | .halt => { t with halted := true }

theorem bstep_eq (Q : ClusterDecomp.Program) (ω : ℕ → Bool) (s : ClusterDecomp.State)
    (i : ClusterDecomp.Instr) (hf : Q[s.core.pc]? = some i) (hh : s.halted = false) :
    ClusterDecomp.step Q ω s = bexec ω i s := by
  unfold ClusterDecomp.step
  rw [if_neg (by simp [hh]), hf]
  cases i with
  | core ci =>
    have h2 : (ClusterDecomp.coreProgram Q)[s.core.pc]? = some ci := by
      unfold ClusterDecomp.coreProgram; rw [List.getElem?_map, hf]; rfl
    rw [coreExec_eq _ _ _ h2]; rfl
  | _ => rfl

noncomputable def exec (ω : Tape) (i : Instr) (s : State) : State :=
  match i with
  | .sqrt d a =>
    { s with base := { s.base with
        work := s.base.work + 1
        core := { s.base.core with
          pc := s.base.core.pc + 1
          regs := Function.update s.base.core.regs d (Real.sqrt (s.base.core.regs a)) } } }
  | .gauss d =>
    { base := { s.base with
        work := s.base.work + 1
        core := { s.base.core with
          pc := s.base.core.pc + 1
          regs := Function.update s.base.core.regs d (ω.2 s.gaussianCursor) } }
      gaussianCursor := s.gaussianCursor + 1 }
  | .base b => { s with base := bexec ω.1 b s.base }

theorem step_eq (P : Program) (ω : Tape) (s : State) (i : Instr)
    (hf : P[s.base.core.pc]? = some i) (hh : s.base.halted = false) :
    step P ω s = exec ω i s := by
  unfold step
  rw [if_neg (by simp [hh]), hf]
  cases i with
  | sqrt d a => rfl
  | gauss d => rfl
  | base b =>
    have h2 : (baseProgram P)[s.base.core.pc]? = some b := by
      unfold baseProgram; rw [List.getElem?_map, hf]; rfl
    show { s with base := ClusterDecomp.step (baseProgram P) ω.1 s.base } = _
    rw [bstep_eq _ _ _ _ h2 hh]; rfl

theorem step_none (P : Program) (ω : Tape) (s : State) (hf : P[s.base.core.pc]? = none)
    (hh : s.base.halted = false) :
    step P ω s = { s with base := { s.base with work := s.base.work + 1 } } := by
  unfold step
  rw [if_neg (by simp [hh]), hf]
  show { s with base := ClusterDecomp.step (baseProgram P) ω.1 s.base } = _
  have h2 : (baseProgram P)[s.base.core.pc]? = none := by
    unfold baseProgram; rw [List.getElem?_map, hf]; rfl
  unfold ClusterDecomp.step
  rw [if_neg (by simp [hh]), h2]

theorem run_two (P : Program) (s : State) (ω : Tape) :
    run P s ω 2 = step P ω (step P ω s) := rfl

theorem run_one (P : Program) (s : State) (ω : Tape) : run P s ω 1 = step P ω s := rfl


/-- A non-halted state given by its fields. -/
abbrev mkS (pc : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ) (im : ℤ → ℤ) (c w g : ℕ) : State :=
  ⟨⟨⟨pc, r, p, m⟩, im, c, false, w⟩, g⟩

theorem step_mkS (Q : Program) (ω : Tape) (pc : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) (i : Instr) (hf : Q[pc]? = some i) :
    step Q ω (mkS pc r p m im c w g) = exec ω i (mkS pc r p m im c w g) :=
  step_eq Q ω _ i hf rfl

theorem step_mkS_none (Q : Program) (ω : Tape) (pc : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) (hf : Q[pc]? = none) :
    step Q ω (mkS pc r p m im c w g) = mkS pc r p m im c (w + 1) g :=
  step_none Q ω _ hf rfl

theorem two_mkS (Q : Program) (ω : Tape) (pc : ℕ) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) (i0 i1 : Instr) (h0 : Q[pc]? = some i0)
    (h1 : Q[(exec ω i0 (mkS pc r p m im c w g)).base.core.pc]? = some i1)
    (hh1 : (exec ω i0 (mkS pc r p m im c w g)).base.halted = false) :
    run Q (mkS pc r p m im c w g) ω 2 = exec ω i1 (exec ω i0 (mkS pc r p m im c w g)) := by
  rw [run_two, step_mkS Q ω pc r p m im c w g i0 h0, step_eq Q ω _ i1 h1 hh1]

theorem run_front (P : Program) (s : State) (ω : Tape) (k : ℕ) :
    run P s ω (k + 1) = run P (step P ω s) ω k := by
  unfold run; rw [Function.iterate_succ_apply]

theorem run_zero (P : Program) (s : State) (ω : Tape) : run P s ω 0 = s := rfl

/-! ## Fetching from the relocated program -/

theorem transInstr_length (T off post : ℕ) (i : Instr) : (transInstr T off post i).length = 2 := by
  unfold transInstr; split <;> rfl

theorem flatMap_get2 {α β : Type*} (f : α → List β) (hf : ∀ x, (f x).length = 2) (l : List α)
    (i j : ℕ) (hj : j < 2) : (l.flatMap f)[2 * i + j]? = (l[i]?).bind (fun x => (f x)[j]?) := by
  induction l generalizing i with
  | nil => simp
  | cons x l ih =>
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      rw [List.getElem?_append_left (by rw [hf]; omega)]; simp
    | succ i =>
      rw [List.getElem?_append_right (by rw [hf]; omega), hf,
        show 2 * (i + 1) + j - 2 = 2 * i + j by omega, ih]
      simp

theorem prepost_length (A : ℕ) : (preCode A offs ++ postCode).length = offs := by
  simp [preCode, postCode, offs]

theorem fetch_trans (A : ℕ) (P : Program) (i j : ℕ) (hj : j < 2) :
    (fullProg A P)[offs + 2 * i + j]? =
      (P[i]?).bind (fun x => (transInstr (scratch P) offs postStart x)[j]?) := by
  unfold fullProg
  rw [List.getElem?_append_right (by rw [prepost_length]; omega), prepost_length,
    show offs + 2 * i + j - offs = 2 * i + j by omega]
  exact flatMap_get2 _ (transInstr_length _ _ _) P i j hj

theorem ptrIdx_lt (P : Program) (i : Instr) (h : i ∈ P) : ptrIdx i < scratch P := by
  unfold scratch
  have := List.le_sum_of_mem (List.mem_map.2 ⟨i, h, rfl⟩ : ptrIdx i ∈ P.map ptrIdx)
  omega

theorem upd_T {T : ℕ} {p p' : ℕ → ℤ} (h : ∀ q, q ≠ T → p' q = p q) (v : ℤ) :
    ∀ q, q ≠ T → Function.update p' T v q = p q := by
  intro q hq; rw [Function.update_of_ne hq]; exact h q hq

theorem upd_dT {T d : ℕ} {p p' : ℕ → ℤ} (h : ∀ q, q ≠ T → p' q = p q) (hd : d ≠ T) (x v : ℤ) :
    ∀ q, q ≠ T → Function.update (Function.update p' d x) T v q = Function.update p d x q := by
  intro q hq
  rw [Function.update_of_ne hq]
  by_cases hqd : q = d
  · subst hqd; simp
  · rw [Function.update_of_ne hqd, Function.update_of_ne hqd]; exact h q hq

theorem memE_store {m m' : ℤ → ℝ} (h : ∀ z, m' (2 * z) = m z) (p : ℤ) (v : ℝ) :
    ∀ z, Function.update m' (p + p) v (2 * z) = Function.update m p v z := by
  intro z
  by_cases hz : z = p
  · subst hz; rw [show z + z = 2 * z by ring]; simp
  · rw [Function.update_of_ne (by omega), Function.update_of_ne hz]; exact h z

theorem memO_store {m' : ℤ → ℝ} {D : ℤ → ℝ} (h : ∀ z, m' (2 * z + 1) = D z) (p : ℤ) (v : ℝ) :
    ∀ z, Function.update m' (p + p) v (2 * z + 1) = D z := by
  intro z; rw [Function.update_of_ne (by omega)]; exact h z

theorem fullProg_admissible (A : ℕ) (P : Program) (hP : Admissible P) :
    Admissible (fullProg A P) := by
  unfold Admissible ClusterDecomp.Admissible at *
  intro op hop
  simp only [baseProgram, List.mem_map] at hop hP
  obtain ⟨i, hi, rfl⟩ := hop
  simp only [fullProg, List.mem_append, List.mem_flatMap] at hi
  rcases hi with (hi | hi) | ⟨j, hj, hi⟩
  · simp only [preCode, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h <;> subst h
    all_goals first
      | trivial
      | exact ⟨0, Rat.cast_zero.symm⟩
      | exact ⟨1, Rat.cast_one.symm⟩
      | exact ⟨(A : ℚ), (Rat.cast_natCast A).symm⟩
  · simp only [postCode, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h <;> subst h
    all_goals first
      | trivial
      | exact ⟨0, Rat.cast_zero.symm⟩
      | exact ⟨1, Rat.cast_one.symm⟩
  · have hPj := hP _ ⟨j, hj, rfl⟩
    cases j with
    | sqrt d a =>
      unfold transInstr at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h <;> subst h
      all_goals first
        | trivial
        | exact ⟨0, Rat.cast_zero.symm⟩
    | gauss d =>
      unfold transInstr at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with h | h <;> subst h
      all_goals first
        | trivial
        | exact ⟨0, Rat.cast_zero.symm⟩
    | base b =>
      cases b with
      | core c =>
        cases c <;> unfold transInstr at hi <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi <;>
          rcases hi with h | h <;> subst h
        all_goals first
          | trivial
          | exact hPj
          | exact hPj.elim
      | _ =>
        unfold transInstr at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with h | h <;> subst h
        all_goals trivial

/-- One step of `P` is simulated by two steps of `fullProg` (or one step into the
post-processing for `halt`). -/
theorem sim_step (A : ℕ) (P : Program) (hP : Admissible P) (D : ℤ → ℝ) (K : ℕ) (ω : Tape)
    (s s' : State) (h : Sim (scratch P) offs D K s s') :
    (P[s.base.core.pc]? ≠ some (.base .halt) →
      Sim (scratch P) offs D K (step P ω s) (run (fullProg A P) s' ω 2)) ∧
    (P[s.base.core.pc]? = some (.base .halt) →
      (step P ω s).base.halted = true ∧ (step P ω s).base.work = s.base.work + 1 ∧
      (step P ω s).base.integerMemory = s.base.integerMemory ∧
      (run (fullProg A P) s' ω 1).base.core.pc = postStart ∧
      (run (fullProg A P) s' ω 1).base.halted = false ∧
      (run (fullProg A P) s' ω 1).base.work = s'.base.work + 1 ∧
      (run (fullProg A P) s' ω 1).base.core.mem = s'.base.core.mem ∧
      (run (fullProg A P) s' ω 1).base.integerMemory = s'.base.integerMemory) := by
  obtain ⟨⟨⟨pc, regs, ptrs, mem⟩, imem, cur, hl, w⟩, g⟩ := s
  obtain ⟨⟨⟨pc', regs', ptrs', mem'⟩, imem', cur', hl', w'⟩, g'⟩ := s'
  obtain ⟨hpc, hregs, hptrs, hmemE, hmemO, himem, hcur, hgcur, hh', hh, hwork⟩ := h
  simp only at hpc hregs hptrs hmemE hmemO himem hcur hgcur hh' hh hwork
  subst hpc hregs himem hcur hgcur hh' hh hwork
  have hf0 := fetch_trans A P pc 0 (by norm_num)
  have hf1 := fetch_trans A P pc 1 (by norm_num)
  rw [Nat.add_zero] at hf0
  simp only
  rcases hP' : P[pc]? with _ | ins
  · rw [hP'] at hf0
    simp only [Option.bind_none] at hf0
    refine ⟨fun _ => ?_, fun h => by cases h⟩
    rw [step_mkS_none P ω _ _ _ _ _ _ _ _ hP', run_two, step_mkS_none _ ω _ _ _ _ _ _ _ _ hf0,
      step_mkS_none _ ω _ _ _ _ _ _ _ _ hf0]
    exact ⟨rfl, rfl, hptrs, hmemE, hmemO, rfl, rfl, rfl, rfl, rfl, by simp only; omega⟩
  · rw [hP'] at hf0 hf1
    simp only [Option.bind_some] at hf0 hf1
    have hmem : ins ∈ P := List.mem_of_getElem? hP'
    have hlt := ptrIdx_lt P ins hmem
    have hPi := hP _ (List.mem_map.2 ⟨ins, hmem, rfl⟩)
    rw [step_mkS P ω _ _ _ _ _ _ _ _ ins hP']
    cases ins with
    | sqrt d a =>
      refine ⟨fun _ => ?_, fun h => by cases h⟩
      rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
      exact ⟨by simp only [exec, bexec, coreExec]; omega, rfl, upd_T hptrs 0, hmemE, hmemO,
        rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
    | gauss d =>
      refine ⟨fun _ => ?_, fun h => by cases h⟩
      rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
      exact ⟨by simp only [exec, bexec, coreExec]; omega, rfl, upd_T hptrs 0, hmemE, hmemO,
        rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
    | base b =>
      cases b with
      | halt =>
        refine ⟨fun hne => absurd rfl hne, fun _ => ?_⟩
        rw [run_one, step_mkS _ ω _ _ _ _ _ _ _ _ _ hf0]
        simp [exec, bexec, coreExec, postStart]
      | coin d =>
        refine ⟨fun _ => ?_, fun h => by cases h⟩
        rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
        exact ⟨by simp only [exec, bexec, coreExec]; omega, rfl, upd_T hptrs 0, hmemE, hmemO,
          rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
      | pointerReal d a =>
        refine ⟨fun _ => ?_, fun h => by cases h⟩
        simp only [ptrIdx] at hlt
        rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
        refine ⟨by simp only [exec, bexec, coreExec]; omega, ?_, upd_T hptrs 0, hmemE, hmemO,
          rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
        simp only [exec, bexec, coreExec]; rw [hptrs a (by omega)]
      | integerStore a b =>
        refine ⟨fun _ => ?_, fun h => by cases h⟩
        simp only [ptrIdx] at hlt
        rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
        refine ⟨by simp only [exec, bexec, coreExec]; omega, rfl, upd_T hptrs 0, hmemE, hmemO,
          ?_, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
        simp only [exec, bexec, coreExec]; rw [hptrs a (by omega), hptrs b (by omega)]
      | integerLoad d a =>
        refine ⟨fun _ => ?_, fun h => by cases h⟩
        simp only [ptrIdx] at hlt
        rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
        refine ⟨by simp only [exec, bexec, coreExec]; omega, rfl, ?_, hmemE, hmemO,
          rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
        simp only [exec, bexec, coreExec]; rw [hptrs a (by omega)]
        exact upd_dT hptrs (by omega) _ 0
      | pointerAdd d a b =>
        refine ⟨fun _ => ?_, fun h => by cases h⟩
        simp only [ptrIdx] at hlt
        rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
        refine ⟨by simp only [exec, bexec, coreExec]; omega, rfl, ?_, hmemE, hmemO,
          rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
        simp only [exec, bexec, coreExec]; rw [hptrs a (by omega), hptrs b (by omega)]
        exact upd_dT hptrs (by omega) _ 0
      | pointerSub d a b =>
        refine ⟨fun _ => ?_, fun h => by cases h⟩
        simp only [ptrIdx] at hlt
        rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
        refine ⟨by simp only [exec, bexec, coreExec]; omega, rfl, ?_, hmemE, hmemO,
          rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
        simp only [exec, bexec, coreExec]; rw [hptrs a (by omega), hptrs b (by omega)]
        exact upd_dT hptrs (by omega) _ 0
      | core c =>
        cases c with
        | accept => exact (hPi : False).elim
        | reject => exact (hPi : False).elim
        | const d v =>
          refine ⟨fun _ => ?_, fun h => by cases h⟩
          rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
          exact ⟨by simp only [exec, bexec, coreExec]; omega, rfl, upd_T hptrs 0, hmemE, hmemO,
            rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
        | add d i j =>
          refine ⟨fun _ => ?_, fun h => by cases h⟩
          rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
          exact ⟨by simp only [exec, bexec, coreExec]; omega, rfl, upd_T hptrs 0, hmemE, hmemO,
            rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
        | sub d i j =>
          refine ⟨fun _ => ?_, fun h => by cases h⟩
          rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
          exact ⟨by simp only [exec, bexec, coreExec]; omega, rfl, upd_T hptrs 0, hmemE, hmemO,
            rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
        | mul d i j =>
          refine ⟨fun _ => ?_, fun h => by cases h⟩
          rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
          exact ⟨by simp only [exec, bexec, coreExec]; omega, rfl, upd_T hptrs 0, hmemE, hmemO,
            rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
        | div d i j =>
          refine ⟨fun _ => ?_, fun h => by cases h⟩
          rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
          exact ⟨by simp only [exec, bexec, coreExec]; omega, rfl, upd_T hptrs 0, hmemE, hmemO,
            rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
        | load d q =>
          refine ⟨fun _ => ?_, fun h => by cases h⟩
          simp only [ptrIdx] at hlt
          rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
          refine ⟨by simp only [exec, bexec, coreExec]; omega, ?_, upd_T hptrs _, hmemE, hmemO,
            rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
          simp only [exec, bexec, coreExec, Function.update_self]
          rw [hptrs q (by omega), show ptrs q + ptrs q = 2 * ptrs q by ring, hmemE]
        | store q i =>
          refine ⟨fun _ => ?_, fun h => by cases h⟩
          simp only [ptrIdx] at hlt
          rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
          refine ⟨by simp only [exec, bexec, coreExec]; omega, rfl, upd_T hptrs _, ?_, ?_,
            rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
          · simp only [exec, bexec, coreExec, Function.update_self]
            rw [hptrs q (by omega)]; exact memE_store hmemE _ _
          · simp only [exec, bexec, coreExec, Function.update_self]
            exact memO_store hmemO _ _
        | pset q c =>
          refine ⟨fun _ => ?_, fun h => by cases h⟩
          simp only [ptrIdx] at hlt
          rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
          exact ⟨by simp only [exec, bexec, coreExec]; omega, rfl, upd_dT hptrs (by omega) _ 0,
            hmemE, hmemO, rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
        | pcopy q q' =>
          refine ⟨fun _ => ?_, fun h => by cases h⟩
          simp only [ptrIdx] at hlt
          rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
          refine ⟨by simp only [exec, bexec, coreExec]; omega, rfl, ?_,
            hmemE, hmemO, rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
          simp only [exec, bexec, coreExec]; rw [hptrs q' (by omega)]
          exact upd_dT hptrs (by omega) _ 0
        | pinc q =>
          refine ⟨fun _ => ?_, fun h => by cases h⟩
          simp only [ptrIdx] at hlt
          rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
          refine ⟨by simp only [exec, bexec, coreExec]; omega, rfl, ?_,
            hmemE, hmemO, rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
          simp only [exec, bexec, coreExec]; rw [hptrs q (by omega)]
          exact upd_dT hptrs (by omega) _ 0
        | pdec q =>
          refine ⟨fun _ => ?_, fun h => by cases h⟩
          simp only [ptrIdx] at hlt
          rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
          refine ⟨by simp only [exec, bexec, coreExec]; omega, rfl, ?_,
            hmemE, hmemO, rfl, rfl, rfl, rfl, rfl, by simp only [exec, bexec, coreExec]; omega⟩
          simp only [exec, bexec, coreExec]; rw [hptrs q (by omega)]
          exact upd_dT hptrs (by omega) _ 0
        | jle i t =>
          refine ⟨fun _ => ?_, fun h => by cases h⟩
          rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
          simp only [exec, bexec, coreExec]
          split_ifs with hc
          · try simp only [hc, if_true, ite_true]
            exact ⟨by first | rfl | (simp only; omega) | omega, rfl, upd_T hptrs _, hmemE, hmemO, rfl, rfl,
              rfl, rfl, rfl, by first | rfl | (simp only; omega) | omega⟩
          · try simp only [hc, if_false, ite_false]
            exact ⟨by first | rfl | (simp only; omega) | omega, rfl, upd_T hptrs _, hmemE, hmemO, rfl, rfl,
              rfl, rfl, rfl, by first | rfl | (simp only; omega) | omega⟩
        | pjle q q' t =>
          refine ⟨fun _ => ?_, fun h => by cases h⟩
          simp only [ptrIdx] at hlt
          rw [two_mkS _ ω _ _ _ _ _ _ _ _ _ _ hf0 hf1 rfl]
          simp only [exec, bexec, coreExec, Function.update_of_ne (show q ≠ scratch P by omega),
            Function.update_of_ne (show q' ≠ scratch P by omega), hptrs q (by omega),
            hptrs q' (by omega)]
          split_ifs with hc
          · try simp only [hc, if_true, ite_true]
            exact ⟨by first | rfl | (simp only; omega) | omega, rfl, upd_T hptrs _, hmemE, hmemO, rfl, rfl,
              rfl, rfl, rfl, by first | rfl | (simp only; omega) | omega⟩
          · try simp only [hc, if_false, ite_false]
            exact ⟨by first | rfl | (simp only; omega) | omega, rfl, upd_T hptrs _, hmemE, hmemO, rfl, rfl,
              rfl, rfl, rfl, by first | rfl | (simp only; omega) | omega⟩

theorem stp0 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 0 r p m im c w g) =
      mkS 1 r (Function.update p 1 ((-1))) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 0 r p m im c w g) _ rfl rfl]; rfl

theorem stp1 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 1 r p m im c w g) =
      mkS 2 r (Function.update p 2 (1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 1 r p m im c w g) _ rfl rfl]; rfl

theorem stp2 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 2 r p m im c w g) =
      mkS 3 r (Function.update p 3 (im (p 0))) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 2 r p m im c w g) _ rfl rfl]; rfl

theorem stp3 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 3 r p m im c w g) =
      mkS 4 r (Function.update p 4 (im (p 2))) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 3 r p m im c w g) _ rfl rfl]; rfl

theorem stp4 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 4 r p m im c w g) =
      mkS 5 r (Function.update p 5 (p 4 + p 3)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 4 r p m im c w g) _ rfl rfl]; rfl

theorem stp5 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 5 r p m im c w g) =
      mkS 6 r (Function.update p 5 (p 5 + 1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 5 r p m im c w g) _ rfl rfl]; rfl

theorem stp6 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 6 r p m im c w g) =
      if p 5 ≤ p 1 then mkS 12 r p m im c (w + 1) g else mkS 7 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 6 r p m im c w g) _ rfl rfl]; split_ifs with h <;> simp [exec, bexec, coreExec, mkS, h]

theorem stp7 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 7 r p m im c w g) =
      mkS 8 r (Function.update p 6 (p 5 + p 5)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 7 r p m im c w g) _ rfl rfl]; rfl

theorem stp8 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 8 r p m im c w g) =
      mkS 9 (Function.update r 0 (m (p 5))) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 8 r p m im c w g) _ rfl rfl]; rfl

theorem stp9 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 9 r p m im c w g) =
      mkS 10 r p (Function.update m (p 6) (r 0)) im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 9 r p m im c w g) _ rfl rfl]; rfl

theorem stp10 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 10 r p m im c w g) =
      mkS 11 r (Function.update p 5 (p 5 - 1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 10 r p m im c w g) _ rfl rfl]; rfl

theorem stp11 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 11 r p m im c w g) =
      mkS 6 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 11 r p m im c w g) _ rfl rfl]; simp [exec, bexec, coreExec, mkS]

theorem stp12 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 12 r p m im c w g) =
      mkS 13 (Function.update r 7 (((p 3 : ℤ) : ℝ))) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 12 r p m im c w g) _ rfl rfl]; rfl

theorem stp13 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 13 r p m im c w g) =
      mkS 14 (Function.update r 8 ((A : ℝ))) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 13 r p m im c w g) _ rfl rfl]; rfl

theorem stp14 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 14 r p m im c w g) =
      mkS 15 (Function.update r 1 (r 8 * r 7)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 14 r p m im c w g) _ rfl rfl]; rfl

theorem stp15 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 15 r p m im c w g) =
      mkS 16 (Function.update r 1 (r 1 * r 7)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 15 r p m im c w g) _ rfl rfl]; rfl

theorem stp16 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 16 r p m im c w g) =
      mkS 17 (Function.update r 1 (r 1 * r 7)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 16 r p m im c w g) _ rfl rfl]; rfl

theorem stp17 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 17 r p m im c w g) =
      mkS 18 (Function.update r 1 (r 1 * r 7)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 17 r p m im c w g) _ rfl rfl]; rfl

theorem stp18 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 18 r p m im c w g) =
      mkS 19 (Function.update r 1 (r 1 * r 7)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 18 r p m im c w g) _ rfl rfl]; rfl

theorem stp19 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 19 r p m im c w g) =
      mkS 20 (Function.update r 1 (r 1 * r 7)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 19 r p m im c w g) _ rfl rfl]; rfl

theorem stp20 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 20 r p m im c w g) =
      mkS 21 (Function.update r 6 (1)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 20 r p m im c w g) _ rfl rfl]; rfl

theorem stp21 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 21 r p m im c w g) =
      mkS 22 (Function.update r 2 (1)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 21 r p m im c w g) _ rfl rfl]; rfl

theorem stp22 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 22 r p m im c w g) =
      mkS 23 r (Function.update p 5 (p 4 + p 4)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 22 r p m im c w g) _ rfl rfl]; rfl

theorem stp23 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 23 r p m im c w g) =
      mkS 24 r (Function.update p 7 (p 3)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 23 r p m im c w g) _ rfl rfl]; rfl

theorem stp24 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 24 r p m im c w g) =
      if p 7 ≤ p 0 then mkS 32 r p m im c (w + 1) g else mkS 25 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 24 r p m im c w g) _ rfl rfl]; split_ifs with h <;> simp [exec, bexec, coreExec, mkS, h]

theorem stp25 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 25 r p m im c w g) =
      mkS 26 (Function.update r 0 (m (p 5))) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 25 r p m im c w g) _ rfl rfl]; rfl

theorem stp26 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 26 r p m im c w g) =
      mkS 27 (Function.update r 3 (r 0 / r 0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 26 r p m im c w g) _ rfl rfl]; rfl

theorem stp27 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 27 r p m im c w g) =
      mkS 28 (Function.update r 2 (r 2 * r 3)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 27 r p m im c w g) _ rfl rfl]; rfl

theorem stp28 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 28 r p m im c w g) =
      mkS 29 r (Function.update p 5 (p 5 + 1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 28 r p m im c w g) _ rfl rfl]; rfl

theorem stp29 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 29 r p m im c w g) =
      mkS 30 r (Function.update p 5 (p 5 + 1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 29 r p m im c w g) _ rfl rfl]; rfl

theorem stp30 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 30 r p m im c w g) =
      mkS 31 r (Function.update p 7 (p 7 - 1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 30 r p m im c w g) _ rfl rfl]; rfl

theorem stp31 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 31 r p m im c w g) =
      mkS 24 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 31 r p m im c w g) _ rfl rfl]; simp [exec, bexec, coreExec, mkS]

theorem stp32 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 32 r p m im c w g) =
      mkS 33 (Function.update r 3 (r 6 - r 1)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 32 r p m im c w g) _ rfl rfl]; rfl

theorem stp33 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 33 r p m im c w g) =
      mkS 34 (Function.update r 3 (r 2 * r 3)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 33 r p m im c w g) _ rfl rfl]; rfl

theorem stp34 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 34 r p m im c w g) =
      mkS 35 (Function.update r 1 (r 1 + r 3)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 34 r p m im c w g) _ rfl rfl]; rfl

theorem stp35 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 35 r p m im c w g) =
      mkS 36 r (Function.update p 5 (p 4 + p 4)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 35 r p m im c w g) _ rfl rfl]; rfl

theorem stp36 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 36 r p m im c w g) =
      mkS 37 r (Function.update p 8 (1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 36 r p m im c w g) _ rfl rfl]; rfl

theorem stp37 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 37 r p m im c w g) =
      mkS 38 r (Function.update p 7 (p 3)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 37 r p m im c w g) _ rfl rfl]; rfl

theorem stp38 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 38 r p m im c w g) =
      if p 7 ≤ p 0 then mkS 52 r p m im c (w + 1) g else mkS 39 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 38 r p m im c w g) _ rfl rfl]; split_ifs with h <;> simp [exec, bexec, coreExec, mkS, h]

theorem stp39 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 39 r p m im c w g) =
      mkS 40 (Function.update r 0 (m (p 5))) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 39 r p m im c w g) _ rfl rfl]; rfl

theorem stp40 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 40 r p m im c w g) =
      mkS 41 r p (Function.update m (p 8) (r 0)) im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 40 r p m im c w g) _ rfl rfl]; rfl

theorem stp41 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 41 r p m im c w g) =
      mkS 42 (Function.update r 3 (r 1 * r 0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 41 r p m im c w g) _ rfl rfl]; rfl

theorem stp42 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 42 r p m im c w g) =
      mkS 43 (Function.update r 2 (r 0 / r 0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 42 r p m im c w g) _ rfl rfl]; rfl

theorem stp43 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 43 r p m im c w g) =
      mkS 44 (Function.update r 2 (r 6 - r 2)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 43 r p m im c w g) _ rfl rfl]; rfl

theorem stp44 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 44 r p m im c w g) =
      mkS 45 (Function.update r 3 (r 3 + r 2)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 44 r p m im c w g) _ rfl rfl]; rfl

theorem stp45 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 45 r p m im c w g) =
      mkS 46 r p (Function.update m (p 5) (r 3)) im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 45 r p m im c w g) _ rfl rfl]; rfl

theorem stp46 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 46 r p m im c w g) =
      mkS 47 r (Function.update p 5 (p 5 + 1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 46 r p m im c w g) _ rfl rfl]; rfl

theorem stp47 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 47 r p m im c w g) =
      mkS 48 r (Function.update p 5 (p 5 + 1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 47 r p m im c w g) _ rfl rfl]; rfl

theorem stp48 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 48 r p m im c w g) =
      mkS 49 r (Function.update p 8 (p 8 + 1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 48 r p m im c w g) _ rfl rfl]; rfl

theorem stp49 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 49 r p m im c w g) =
      mkS 50 r (Function.update p 8 (p 8 + 1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 49 r p m im c w g) _ rfl rfl]; rfl

theorem stp50 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 50 r p m im c w g) =
      mkS 51 r (Function.update p 7 (p 7 - 1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 50 r p m im c w g) _ rfl rfl]; rfl

theorem stp51 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 51 r p m im c w g) =
      mkS 38 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 51 r p m im c w g) _ rfl rfl]; simp [exec, bexec, coreExec, mkS]

theorem stp52 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 52 r p m im c w g) =
      mkS 53 (Function.update r 0 (m (p 5))) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 52 r p m im c w g) _ rfl rfl]; rfl

theorem stp53 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 53 r p m im c w g) =
      mkS 54 (Function.update r 0 (r 0 / r 1)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 53 r p m im c w g) _ rfl rfl]; rfl

theorem stp54 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 54 r p m im c w g) =
      mkS 55 r p (Function.update m (p 5) (r 0)) im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 54 r p m im c w g) _ rfl rfl]; rfl

theorem stp55 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 55 r p m im c w g) =
      mkS 56 r p (Function.update m (p 1) (r 7)) im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 55 r p m im c w g) _ rfl rfl]; rfl

theorem stp56 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 56 r p m im c w g) =
      mkS 57 r (Function.update p 1 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 56 r p m im c w g) _ rfl rfl]; rfl

theorem stp57 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 57 r p m im c w g) =
      mkS 58 r (Function.update p 2 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 57 r p m im c w g) _ rfl rfl]; rfl

theorem stp58 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 58 r p m im c w g) =
      mkS 59 r (Function.update p 3 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 58 r p m im c w g) _ rfl rfl]; rfl

theorem stp59 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 59 r p m im c w g) =
      mkS 60 r (Function.update p 4 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 59 r p m im c w g) _ rfl rfl]; rfl

theorem stp60 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 60 r p m im c w g) =
      mkS 61 r (Function.update p 5 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 60 r p m im c w g) _ rfl rfl]; rfl

theorem stp61 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 61 r p m im c w g) =
      mkS 62 r (Function.update p 6 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 61 r p m im c w g) _ rfl rfl]; rfl

theorem stp62 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 62 r p m im c w g) =
      mkS 63 r (Function.update p 7 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 62 r p m im c w g) _ rfl rfl]; rfl

theorem stp63 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 63 r p m im c w g) =
      mkS 64 r (Function.update p 8 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 63 r p m im c w g) _ rfl rfl]; rfl

theorem stp64 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 64 r p m im c w g) =
      mkS 65 (Function.update r 0 (0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 64 r p m im c w g) _ rfl rfl]; rfl

theorem stp65 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 65 r p m im c w g) =
      mkS 66 (Function.update r 1 (0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 65 r p m im c w g) _ rfl rfl]; rfl

theorem stp66 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 66 r p m im c w g) =
      mkS 67 (Function.update r 2 (0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 66 r p m im c w g) _ rfl rfl]; rfl

theorem stp67 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 67 r p m im c w g) =
      mkS 68 (Function.update r 3 (0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 67 r p m im c w g) _ rfl rfl]; rfl

theorem stp68 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 68 r p m im c w g) =
      mkS 69 (Function.update r 6 (0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 68 r p m im c w g) _ rfl rfl]; rfl

theorem stp69 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 69 r p m im c w g) =
      mkS 70 (Function.update r 7 (0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 69 r p m im c w g) _ rfl rfl]; rfl

theorem stp70 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 70 r p m im c w g) =
      mkS 71 (Function.update r 8 (0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 70 r p m im c w g) _ rfl rfl]; rfl

theorem stp71 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 71 r p m im c w g) =
      mkS offs r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 71 r p m im c w g) _ rfl rfl]; simp [exec, bexec, coreExec, mkS]

theorem stp72 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 72 r p m im c w g) =
      mkS 73 r (Function.update p 0 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 72 r p m im c w g) _ rfl rfl]; rfl

theorem stp73 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 73 r p m im c w g) =
      mkS 74 r (Function.update p 1 ((-1))) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 73 r p m im c w g) _ rfl rfl]; rfl

theorem stp74 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 74 r p m im c w g) =
      mkS 75 r (Function.update p 8 (1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 74 r p m im c w g) _ rfl rfl]; rfl

theorem stp75 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 75 r p m im c w g) =
      mkS 76 r (Function.update p 9 ((-1))) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 75 r p m im c w g) _ rfl rfl]; rfl

theorem stp76 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 76 r p m im c w g) =
      mkS 77 (Function.update r 11 (m (p 1))) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 76 r p m im c w g) _ rfl rfl]; rfl

theorem stp77 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 77 r p m im c w g) =
      mkS 78 (Function.update r 6 (1)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 77 r p m im c w g) _ rfl rfl]; rfl

theorem stp78 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 78 r p m im c w g) =
      mkS 79 (Function.update r 9 (0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 78 r p m im c w g) _ rfl rfl]; rfl

theorem stp79 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 79 r p m im c w g) =
      mkS 80 (Function.update r 10 (0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 79 r p m im c w g) _ rfl rfl]; rfl

theorem stp80 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 80 r p m im c w g) =
      if r 11 ≤ 0 then mkS 95 r p m im c (w + 1) g else mkS 81 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 80 r p m im c w g) _ rfl rfl]; split_ifs with h <;> simp [exec, bexec, coreExec, mkS, h]

theorem stp81 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 81 r p m im c w g) =
      mkS 82 r (Function.update p 10 (im (p 9))) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 81 r p m im c w g) _ rfl rfl]; rfl

theorem stp82 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 82 r p m im c w g) =
      mkS 83 (Function.update r 0 (((p 10 : ℤ) : ℝ))) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 82 r p m im c w g) _ rfl rfl]; rfl

theorem stp83 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 83 r p m im c w g) =
      mkS 84 (Function.update r 0 (r 0 / r 0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 83 r p m im c w g) _ rfl rfl]; rfl

theorem stp84 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 84 r p m im c w g) =
      mkS 85 (Function.update r 3 (m (p 8))) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 84 r p m im c w g) _ rfl rfl]; rfl

theorem stp85 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 85 r p m im c w g) =
      mkS 86 (Function.update r 4 (r 3 * r 0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 85 r p m im c w g) _ rfl rfl]; rfl

theorem stp86 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 86 r p m im c w g) =
      mkS 87 (Function.update r 9 (r 9 + r 4)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 86 r p m im c w g) _ rfl rfl]; rfl

theorem stp87 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 87 r p m im c w g) =
      mkS 88 (Function.update r 0 (r 6 - r 0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 87 r p m im c w g) _ rfl rfl]; rfl

theorem stp88 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 88 r p m im c w g) =
      mkS 89 (Function.update r 4 (r 3 * r 0)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 88 r p m im c w g) _ rfl rfl]; rfl

theorem stp89 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 89 r p m im c w g) =
      mkS 90 (Function.update r 10 (r 10 + r 4)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 89 r p m im c w g) _ rfl rfl]; rfl

theorem stp90 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 90 r p m im c w g) =
      mkS 91 r (Function.update p 9 (p 9 - 1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 90 r p m im c w g) _ rfl rfl]; rfl

theorem stp91 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 91 r p m im c w g) =
      mkS 92 r (Function.update p 8 (p 8 + 1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 91 r p m im c w g) _ rfl rfl]; rfl

theorem stp92 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 92 r p m im c w g) =
      mkS 93 r (Function.update p 8 (p 8 + 1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 92 r p m im c w g) _ rfl rfl]; rfl

theorem stp93 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 93 r p m im c w g) =
      mkS 94 (Function.update r 11 (r 11 - r 6)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 93 r p m im c w g) _ rfl rfl]; rfl

theorem stp94 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 94 r p m im c w g) =
      mkS 80 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 94 r p m im c w g) _ rfl rfl]; simp [exec, bexec, coreExec, mkS]

theorem stp95 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 95 r p m im c w g) =
      mkS 96 (Function.update r 0 (r 9 - r 10)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 95 r p m im c w g) _ rfl rfl]; rfl

theorem stp96 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 96 r p m im c w g) =
      if r 9 ≤ 0 then mkS 104 r p m im c (w + 1) g else mkS 97 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 96 r p m im c w g) _ rfl rfl]; split_ifs with h <;> simp [exec, bexec, coreExec, mkS, h]

theorem stp97 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 97 r p m im c w g) =
      if r 0 ≤ 0 then mkS 101 r p m im c (w + 1) g else mkS 98 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 97 r p m im c w g) _ rfl rfl]; split_ifs with h <;> simp [exec, bexec, coreExec, mkS, h]

theorem stp98 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 98 r p m im c w g) =
      mkS 99 r (Function.update p 11 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 98 r p m im c w g) _ rfl rfl]; rfl

theorem stp99 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 99 r p m im c w g) =
      mkS 100 r (Function.update p 12 (1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 99 r p m im c w g) _ rfl rfl]; rfl

theorem stp100 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 100 r p m im c w g) =
      mkS 108 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 100 r p m im c w g) _ rfl rfl]; simp [exec, bexec, coreExec, mkS]

theorem stp101 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 101 r p m im c w g) =
      mkS 102 r (Function.update p 11 (1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 101 r p m im c w g) _ rfl rfl]; rfl

theorem stp102 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 102 r p m im c w g) =
      mkS 103 r (Function.update p 12 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 102 r p m im c w g) _ rfl rfl]; rfl

theorem stp103 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 103 r p m im c w g) =
      mkS 108 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 103 r p m im c w g) _ rfl rfl]; simp [exec, bexec, coreExec, mkS]

theorem stp104 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 104 r p m im c w g) =
      mkS 105 r (Function.update p 11 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 104 r p m im c w g) _ rfl rfl]; rfl

theorem stp105 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 105 r p m im c w g) =
      mkS 106 r (Function.update p 12 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 105 r p m im c w g) _ rfl rfl]; rfl

theorem stp106 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 106 r p m im c w g) =
      mkS 107 r (Function.update p 10 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 106 r p m im c w g) _ rfl rfl]; rfl

theorem stp107 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 107 r p m im c w g) =
      mkS 108 r (Function.update p 10 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 107 r p m im c w g) _ rfl rfl]; rfl

theorem stp108 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 108 r p m im c w g) =
      mkS 109 r (Function.update p 9 ((-1))) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 108 r p m im c w g) _ rfl rfl]; rfl

theorem stp109 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 109 r p m im c w g) =
      mkS 110 (Function.update r 11 (m (p 1))) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 109 r p m im c w g) _ rfl rfl]; rfl

theorem stp110 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 110 r p m im c w g) =
      if r 11 ≤ 0 then mkS 125 r p m im c (w + 1) g else mkS 111 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 110 r p m im c w g) _ rfl rfl]; split_ifs with h <;> simp [exec, bexec, coreExec, mkS, h]

theorem stp111 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 111 r p m im c w g) =
      mkS 112 r (Function.update p 13 (im (p 9))) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 111 r p m im c w g) _ rfl rfl]; rfl

theorem stp112 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 112 r p m im c w g) =
      if p 13 ≤ p 0 then mkS 116 r p m im c (w + 1) g else mkS 113 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 112 r p m im c w g) _ rfl rfl]; split_ifs with h <;> simp [exec, bexec, coreExec, mkS, h]

theorem stp113 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 113 r p m im c w g) =
      mkS 114 r (Function.update p 14 (p 11)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 113 r p m im c w g) _ rfl rfl]; rfl

theorem stp114 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 114 r p m im c w g) =
      mkS 115 r (Function.update p 10 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 114 r p m im c w g) _ rfl rfl]; rfl

theorem stp115 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 115 r p m im c w g) =
      mkS 121 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 115 r p m im c w g) _ rfl rfl]; simp [exec, bexec, coreExec, mkS]

theorem stp116 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 116 r p m im c w g) =
      if p 0 ≤ p 13 then mkS 119 r p m im c (w + 1) g else mkS 117 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 116 r p m im c w g) _ rfl rfl]; split_ifs with h <;> simp [exec, bexec, coreExec, mkS, h]

theorem stp117 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 117 r p m im c w g) =
      mkS 118 r (Function.update p 14 (p 11)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 117 r p m im c w g) _ rfl rfl]; rfl

theorem stp118 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 118 r p m im c w g) =
      mkS 121 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 118 r p m im c w g) _ rfl rfl]; simp [exec, bexec, coreExec, mkS]

theorem stp119 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 119 r p m im c w g) =
      mkS 120 r (Function.update p 14 (p 12)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 119 r p m im c w g) _ rfl rfl]; rfl

theorem stp120 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 120 r p m im c w g) =
      mkS 121 r (Function.update p 10 (0)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 120 r p m im c w g) _ rfl rfl]; rfl

theorem stp121 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 121 r p m im c w g) =
      mkS 122 r p m (Function.update im (p 9) (p 14)) c (w + 1) g :=
  by rw [step_eq _ ω (mkS 121 r p m im c w g) _ rfl rfl]; rfl

theorem stp122 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 122 r p m im c w g) =
      mkS 123 r (Function.update p 9 (p 9 - 1)) m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 122 r p m im c w g) _ rfl rfl]; rfl

theorem stp123 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 123 r p m im c w g) =
      mkS 124 (Function.update r 11 (r 11 - r 6)) p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 123 r p m im c w g) _ rfl rfl]; rfl

theorem stp124 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 124 r p m im c w g) =
      mkS 110 r p m im c (w + 1) g :=
  by rw [step_eq _ ω (mkS 124 r p m im c w g) _ rfl rfl]; simp [exec, bexec, coreExec, mkS]

theorem stp125 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    step (fullProg A P) ω (mkS 125 r p m im c w g) =
      ⟨⟨⟨126, r, p, m⟩, im, c, true, w + 1⟩, g⟩ :=
  by rw [step_eq _ ω (mkS 125 r p m im c w g) _ rfl rfl]; rfl

/-! ## Prologue -/

/-- Real memory initialised from a list. -/
noncomputable def rmem (l : List ℝ) : ℤ → ℝ := fun z => if 0 ≤ z then l.getD z.toNat 0 else 0

/-- Memory after the top-down copy `M[2i] := M[i]` for all `i ≥ j`. -/
noncomputable def copyMem (m0 : ℤ → ℝ) (j : ℤ) : ℤ → ℝ :=
  fun z => if 2 ∣ z ∧ j ≤ z / 2 then m0 (z / 2) else m0 z

/-- Memory after the first `k` rounds of the weight-perturbation loop. -/
noncomputable def tr3 (m : ℤ → ℝ) (B : ℤ) (N : ℝ) (k : ℕ) : ℤ → ℝ := fun z =>
  if 2 ∣ z ∧ B ≤ z ∧ z < B + 2 * k then N * m z + (1 - m z / m z)
  else if ¬ 2 ∣ z ∧ 1 ≤ z ∧ z < 2 * k then m (B + z - 1) else m z

theorem copyMem_step (m0 : ℤ → ℝ) (i : ℤ) (hi : 0 ≤ i) :
    Function.update (copyMem m0 (i + 1)) (i + i) (copyMem m0 (i + 1) i) = copyMem m0 i := by
  funext z
  simp only [Function.update_apply, copyMem]
  split_ifs <;> first | rfl | (exfalso; omega) | (subst_vars; congr 1; omega) | (congr 1; omega)

theorem copyMem_full (m0 : ℤ → ℝ) (L : ℤ) (hL : 0 ≤ L) (h : ∀ z, L ≤ z → m0 z = 0) :
    copyMem m0 L = m0 := by
  funext z
  unfold copyMem
  split_ifs with hz
  · rw [h (z / 2) (by omega), h z (by omega)]
  · rfl

theorem copyMem_even (m0 : ℤ → ℝ) (h : ∀ z, z < 0 → m0 z = 0) (z : ℤ) :
    copyMem m0 0 (2 * z) = m0 z := by
  unfold copyMem
  split_ifs with hz
  · rw [show 2 * z / 2 = z by omega]
  · rw [h (2 * z) (by omega), h z (by omega)]

theorem tr3_zero (m : ℤ → ℝ) (B : ℤ) (N : ℝ) : tr3 m B N 0 = m := by
  funext z; unfold tr3; split_ifs <;> first | rfl | omega

theorem tr3_at (m : ℤ → ℝ) (B : ℤ) (N : ℝ) (k : ℕ) (hB : 2 ∣ B) :
    tr3 m B N k (B + 2 * k) = m (B + 2 * k) := by
  unfold tr3; split_ifs <;> first | rfl | omega

theorem tr3_step (m : ℤ → ℝ) (B : ℤ) (N : ℝ) (k : ℕ) (hB : 2 ∣ B) (hB0 : 0 ≤ B) :
    Function.update (Function.update (tr3 m B N k) (2 * (k : ℤ) + 1) (tr3 m B N k (B + 2 * k)))
      (B + 2 * k) (N * tr3 m B N k (B + 2 * k) +
        (1 - tr3 m B N k (B + 2 * k) / tr3 m B N k (B + 2 * k))) = tr3 m B N (k + 1) := by
  rw [tr3_at m B N k hB]
  funext z
  simp only [Function.update_apply, tr3]
  split_ifs <;> first | rfl | (exfalso; omega) | (subst_vars; rfl) |
    (subst_vars; congr 1; omega) | (congr 1; omega)

theorem pre_init (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    ∃ p', run (fullProg A P) (mkS 0 r p m im c w g) ω 6 = mkS 6 r p' m im c (w + 6) g ∧
      p' 0 = p 0 ∧ p' 1 = -1 ∧ p' 3 = im (p 0) ∧ p' 4 = im 1 ∧ p' 5 = im 1 + im (p 0) + 1 ∧
      (∀ q, 9 ≤ q → p' q = p q) := by
  simp only [run_front, run_zero, stp0, stp1, stp2, stp3, stp4, stp5]
  refine ⟨_, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro q hq; simp only [Function.update_apply]; split_ifs <;> first | rfl | omega)
    | simp [Function.update_apply]

theorem pre_iter1 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) (hc : ¬ p 5 ≤ p 1) :
    ∃ r' p', run (fullProg A P) (mkS 6 r p m im c w g) ω 6 =
        mkS 6 r' p' (Function.update m (p 5 + p 5) (m (p 5))) im c (w + 6) g ∧
      p' 5 = p 5 - 1 ∧ p' 0 = p 0 ∧ p' 1 = p 1 ∧ p' 3 = p 3 ∧ p' 4 = p 4 ∧
      (∀ q, 9 ≤ q → p' q = p q) ∧ (∀ k, k ≠ 0 → r' k = r k) := by
  simp only [run_front, run_zero, stp6, hc, if_false, stp7, stp8, stp9, stp10, stp11]
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro q hq; simp only [Function.update_apply]; split_ifs <;> first | rfl | omega)
    | simp [Function.update_apply]

theorem pre_loop1 (A : ℕ) (P : Program) (ω : Tape) (m0 : ℤ → ℝ) (im : ℤ → ℤ) (c g : ℕ) :
    ∀ j : ℕ, ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ), p 5 = (j : ℤ) - 1 → p 1 = -1 →
      ∃ r' p', run (fullProg A P) (mkS 6 r p (copyMem m0 j) im c w g) ω (6 * j) =
          mkS 6 r' p' (copyMem m0 0) im c (w + 6 * j) g ∧
        p' 5 = -1 ∧ p' 0 = p 0 ∧ p' 1 = p 1 ∧ p' 3 = p 3 ∧ p' 4 = p 4 ∧
        (∀ q, 9 ≤ q → p' q = p q) ∧ (∀ k, k ≠ 0 → r' k = r k) := by
  intro j
  induction j with
  | zero =>
    intro r p w h5 h1
    exact ⟨r, p, rfl, by simpa using h5, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | succ j ih =>
    intro r p w h5 h1
    have hc : ¬ p 5 ≤ p 1 := by rw [h5, h1]; omega
    obtain ⟨r1, p1, hrun1, e5, e0, e1, e3, e4, eq, er⟩ :=
      pre_iter1 A P ω r p (copyMem m0 ((j + 1 : ℕ) : ℤ)) im c w g hc
    have hm : Function.update (copyMem m0 ((j + 1 : ℕ) : ℤ)) (p 5 + p 5)
        (copyMem m0 ((j + 1 : ℕ) : ℤ) (p 5)) = copyMem m0 j := by
      rw [h5, show ((j + 1 : ℕ) : ℤ) - 1 = j by push_cast; ring,
        show ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 by push_cast; ring]
      exact copyMem_step m0 j (by positivity)
    rw [hm] at hrun1
    obtain ⟨r', p', hrun, f5, f0, f1, f3, f4, fq, fr⟩ := ih r1 p1 (w + 6)
      (by rw [e5, h5]; push_cast; ring) (by rw [e1, h1])
    refine ⟨r', p', ?_, f5, by rw [f0, e0], by rw [f1, e1], by rw [f3, e3], by rw [f4, e4],
      fun q hq => by rw [fq q hq, eq q hq], fun k hk => by rw [fr k hk, er k hk]⟩
    rw [show 6 * (j + 1) = 6 + 6 * j by ring, run_add, hrun1, hrun]
    congr 1; omega

theorem pre_exit1 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) (h5 : p 5 = -1) (h1 : p 1 = -1) :
    run (fullProg A P) (mkS 6 r p m im c w g) ω 1 = mkS 12 r p m im c (w + 1) g := by
  simp only [run_front, run_zero, stp6, h5, h1, le_refl, if_true]

theorem pre_mid1 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    ∃ r' p', run (fullProg A P) (mkS 12 r p m im c w g) ω 12 = mkS 24 r' p' m im c (w + 12) g ∧
      r' 1 = (A : ℝ) * ((p 3 : ℤ) : ℝ) * ((p 3 : ℤ) : ℝ) * ((p 3 : ℤ) : ℝ) * ((p 3 : ℤ) : ℝ) *
        ((p 3 : ℤ) : ℝ) * ((p 3 : ℤ) : ℝ) ∧
      r' 6 = 1 ∧ r' 2 = 1 ∧ r' 7 = ((p 3 : ℤ) : ℝ) ∧
      p' 5 = p 4 + p 4 ∧ p' 7 = p 3 ∧ p' 0 = p 0 ∧ p' 1 = p 1 ∧ p' 3 = p 3 ∧ p' 4 = p 4 ∧
      (∀ q, 9 ≤ q → p' q = p q) ∧ (∀ k, 9 ≤ k ∨ k = 4 ∨ k = 5 → r' k = r k) := by
  simp only [run_front, run_zero, stp12, stp13, stp14, stp15, stp16, stp17, stp18, stp19, stp20, stp21, stp22, stp23]
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro q hq; simp only [Function.update_apply]; split_ifs <;> first | rfl | omega)
    | simp [Function.update_apply]

theorem pre_iter2 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) (hc : ¬ p 7 ≤ p 0) :
    ∃ r' p', run (fullProg A P) (mkS 24 r p m im c w g) ω 8 = mkS 24 r' p' m im c (w + 8) g ∧
      r' 2 = r 2 * (m (p 5) / m (p 5)) ∧ r' 1 = r 1 ∧ r' 6 = r 6 ∧ r' 7 = r 7 ∧
      p' 5 = p 5 + 1 + 1 ∧ p' 7 = p 7 - 1 ∧ p' 0 = p 0 ∧ p' 1 = p 1 ∧ p' 3 = p 3 ∧ p' 4 = p 4 ∧
      (∀ q, 9 ≤ q → p' q = p q) ∧ (∀ k, 9 ≤ k ∨ k = 4 ∨ k = 5 → r' k = r k) := by
  simp only [run_front, run_zero, stp24, hc, if_false, stp25, stp26, stp27, stp28, stp29, stp30, stp31]
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro q hq; simp only [Function.update_apply]; split_ifs <;> first | rfl | omega)
    | simp [Function.update_apply]

theorem pre_loop2 (A : ℕ) (P : Program) (ω : Tape) (m : ℤ → ℝ) (im : ℤ → ℤ) (c g : ℕ) (B : ℤ) :
    ∀ j k : ℕ, ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ), p 7 = j → p 0 = 0 → p 5 = B + 2 * (k : ℤ) →
      ∃ r' p', run (fullProg A P) (mkS 24 r p m im c w g) ω (8 * j) =
          mkS 24 r' p' m im c (w + 8 * j) g ∧
        r' 2 = r 2 * ∏ i ∈ Finset.range j,
          (m (B + 2 * ((k + i : ℕ) : ℤ)) / m (B + 2 * ((k + i : ℕ) : ℤ))) ∧
        r' 1 = r 1 ∧ r' 6 = r 6 ∧ r' 7 = r 7 ∧ p' 7 = 0 ∧ p' 0 = p 0 ∧ p' 1 = p 1 ∧
        p' 3 = p 3 ∧ p' 4 = p 4 ∧
        (∀ q, 9 ≤ q → p' q = p q) ∧ (∀ k, 9 ≤ k ∨ k = 4 ∨ k = 5 → r' k = r k) := by
  intro j
  induction j with
  | zero =>
    intro k r p w h7 _ _
    exact ⟨r, p, rfl, by simp, rfl, rfl, rfl, by simpa using h7, rfl, rfl, rfl, rfl,
      fun _ _ => rfl, fun _ _ => rfl⟩
  | succ j ih =>
    intro k r p w h7 h0 h5
    have hc : ¬ p 7 ≤ p 0 := by rw [h7, h0]; omega
    obtain ⟨r1, p1, hrun1, e2, e1, e6, e7, e5, e7', e0, e1', e3, e4, eq, er⟩ :=
      pre_iter2 A P ω r p m im c w g hc
    obtain ⟨r', p', hrun, f2, f1, f6, f7, f7', f0, f1', f3, f4, fq, fr⟩ := ih (k + 1) r1 p1 (w + 8)
      (by rw [e7', h7]; push_cast; ring) (by rw [e0, h0]) (by rw [e5, h5]; push_cast; ring)
    refine ⟨r', p', ?_, ?_, by rw [f1, e1], by rw [f6, e6], by rw [f7, e7], f7',
      by rw [f0, e0], by rw [f1', e1'], by rw [f3, e3], by rw [f4, e4],
      fun q hq => by rw [fq q hq, eq q hq], fun k hk => by rw [fr k hk, er k hk]⟩
    · rw [show 8 * (j + 1) = 8 + 8 * j by ring, run_add, hrun1, hrun]
      congr 1; omega
    · have h2 : ∏ i ∈ Finset.range j,
          (m (B + 2 * ((k + 1 + i : ℕ) : ℤ)) / m (B + 2 * ((k + 1 + i : ℕ) : ℤ))) =
          ∏ i ∈ Finset.range j,
          (m (B + 2 * ((k + (i + 1) : ℕ) : ℤ)) / m (B + 2 * ((k + (i + 1) : ℕ) : ℤ))) :=
        Finset.prod_congr rfl (fun i _ => by rw [show k + 1 + i = k + (i + 1) by ring])
      rw [f2, e2, h5, h2, Finset.prod_range_succ', Nat.add_zero]
      ring

theorem pre_exit2 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) (h7 : p 7 = 0) (h0 : p 0 = 0) :
    run (fullProg A P) (mkS 24 r p m im c w g) ω 1 = mkS 32 r p m im c (w + 1) g := by
  simp only [run_front, run_zero, stp24, h7, h0, le_refl, if_true]

theorem pre_mid2 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    ∃ r' p', run (fullProg A P) (mkS 32 r p m im c w g) ω 6 = mkS 38 r' p' m im c (w + 6) g ∧
      r' 1 = r 1 + r 2 * (r 6 - r 1) ∧ r' 6 = r 6 ∧ r' 7 = r 7 ∧
      p' 5 = p 4 + p 4 ∧ p' 8 = 1 ∧ p' 7 = p 3 ∧ p' 0 = p 0 ∧ p' 1 = p 1 ∧
      (∀ q, 9 ≤ q → p' q = p q) ∧ (∀ k, 9 ≤ k ∨ k = 4 ∨ k = 5 → r' k = r k) := by
  simp only [run_front, run_zero, stp32, stp33, stp34, stp35, stp36, stp37]
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro q hq; simp only [Function.update_apply]; split_ifs <;> first | rfl | omega)
    | simp [Function.update_apply]

theorem pre_iter3 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) (hc : ¬ p 7 ≤ p 0) :
    ∃ r' p', run (fullProg A P) (mkS 38 r p m im c w g) ω 14 =
        mkS 38 r' p' (Function.update (Function.update m (p 8) (m (p 5))) (p 5)
          (r 1 * m (p 5) + (r 6 - m (p 5) / m (p 5)))) im c (w + 14) g ∧
      r' 1 = r 1 ∧ r' 6 = r 6 ∧ r' 7 = r 7 ∧ p' 5 = p 5 + 1 + 1 ∧ p' 8 = p 8 + 1 + 1 ∧
      p' 7 = p 7 - 1 ∧ p' 0 = p 0 ∧ p' 1 = p 1 ∧
      (∀ q, 9 ≤ q → p' q = p q) ∧ (∀ k, 9 ≤ k ∨ k = 4 ∨ k = 5 → r' k = r k) := by
  simp only [run_front, run_zero, stp38, hc, if_false, stp39, stp40, stp41, stp42, stp43, stp44, stp45, stp46, stp47, stp48, stp49, stp50, stp51]
  refine ⟨_, _, rfl, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro q hq; simp only [Function.update_apply]; split_ifs <;> first | rfl | omega)
    | simp [Function.update_apply]

theorem pre_loop3 (A : ℕ) (P : Program) (ω : Tape) (m : ℤ → ℝ) (im : ℤ → ℤ) (c g : ℕ) (B : ℤ)
    (N : ℝ) (hB : 2 ∣ B) (hB0 : 0 ≤ B) :
    ∀ j k : ℕ, ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ), p 7 = j → p 0 = 0 → p 5 = B + 2 * (k : ℤ) →
      p 8 = 2 * (k : ℤ) + 1 → r 1 = N → r 6 = 1 →
      ∃ r' p', run (fullProg A P) (mkS 38 r p (tr3 m B N k) im c w g) ω (14 * j) =
          mkS 38 r' p' (tr3 m B N (k + j)) im c (w + 14 * j) g ∧
        r' 1 = r 1 ∧ r' 7 = r 7 ∧ p' 7 = 0 ∧ p' 0 = p 0 ∧ p' 1 = p 1 ∧
        p' 5 = B + 2 * ((k + j : ℕ) : ℤ) ∧
        (∀ q, 9 ≤ q → p' q = p q) ∧ (∀ k, 9 ≤ k ∨ k = 4 ∨ k = 5 → r' k = r k) := by
  intro j
  induction j with
  | zero =>
    intro k r p w h7 _ h5 _ _ _
    exact ⟨r, p, rfl, rfl, rfl, by simpa using h7, rfl, rfl, by simpa using h5,
      fun _ _ => rfl, fun _ _ => rfl⟩
  | succ j ih =>
    intro k r p w h7 h0 h5 h8 hr1 hr6
    have hc : ¬ p 7 ≤ p 0 := by rw [h7, h0]; omega
    obtain ⟨r1, p1, hrun1, e1, e6, e7, e5, e8, e7', e0, e1', eq, er⟩ :=
      pre_iter3 A P ω r p (tr3 m B N k) im c w g hc
    rw [h8, h5, hr1, hr6, tr3_step m B N k hB hB0] at hrun1
    obtain ⟨r', p', hrun, f1, f7, f7', f0, f1', f5, fq, fr⟩ := ih (k + 1) r1 p1 (w + 14)
      (by rw [e7', h7]; push_cast; ring) (by rw [e0, h0]) (by rw [e5, h5]; push_cast; ring)
      (by rw [e8, h8]; push_cast; ring) (by rw [e1, hr1]) (by rw [e6, hr6])
    refine ⟨r', p', ?_, by rw [f1, e1], by rw [f7, e7], f7', by rw [f0, e0], by rw [f1', e1'],
      by rw [f5]; push_cast; ring, fun q hq => by rw [fq q hq, eq q hq],
      fun k hk => by rw [fr k hk, er k hk]⟩
    rw [show 14 * (j + 1) = 14 + 14 * j by ring, run_add, hrun1, hrun,
      show k + 1 + j = k + (j + 1) by ring]
    congr 1; omega

theorem pre_exit3 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) (h7 : p 7 = 0) (h0 : p 0 = 0) :
    run (fullProg A P) (mkS 38 r p m im c w g) ω 1 = mkS 52 r p m im c (w + 1) g := by
  simp only [run_front, run_zero, stp38, h7, h0, le_refl, if_true]

theorem pre_final (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    ∃ r' p', run (fullProg A P) (mkS 52 r p m im c w g) ω 20 =
        mkS offs r' p' (Function.update (Function.update m (p 5) (m (p 5) / r 1)) (p 1) (r 7))
          im c (w + 20) g ∧
      (∀ k, r' k = if 9 ≤ k ∨ k = 4 ∨ k = 5 then r k else 0) ∧
      (∀ q, p' q = if q = 0 ∨ 9 ≤ q then p q else 0) := by
  simp only [run_front, run_zero, stp52, stp53, stp54, stp55, stp56, stp57, stp58, stp59, stp60, stp61, stp62, stp63, stp64, stp65, stp66, stp67, stp68, stp69, stp70, stp71]
  refine ⟨_, _, rfl, fun k => ?_, fun q => ?_⟩ <;>
    simp only [Function.update_apply] <;> split_ifs <;> first | rfl | omega

theorem rmem_neg (l : List ℝ) (z : ℤ) (hz : z < 0) : rmem l z = 0 := by
  unfold rmem; rw [if_neg (by omega)]

theorem rmem_large (l : List ℝ) (z : ℤ) (hz : (l.length : ℤ) ≤ z) : rmem l z = 0 := by
  unfold rmem; rw [if_pos (by omega)]
  rw [List.getD_eq_default]; omega

theorem graphReals_length {n : ℕ} (G : Graph n) (π : Fin n → ℝ) (a b : ℝ) :
    (graphReals G π [a, b]).length = G.length + n + 2 := by
  simp [graphReals]; omega

theorem rmem_graph_out {n : ℕ} (G : Graph n) (π π' : Fin n → ℝ) (a a' b : ℝ) (z : ℤ)
    (hz : z < G.length ∨ (G.length : ℤ) + n < z) :
    rmem (graphReals G π [a, b]) z = rmem (graphReals G π' [a', b]) z := by
  unfold rmem
  split_ifs with h0
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    simp only [Int.toNat_natCast]
    unfold graphReals
    rcases hz with hz | hz
    · have hk : k < G.length := by omega
      rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega),
        List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by simp; omega)]
    · rw [List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
      obtain ⟨i, hi⟩ : ∃ i, k - (G.map (fun e => (e.capacity : ℝ)) ++
          (List.finRange n).map π).length = i + 1 := ⟨k - (G.length + n) - 1, by simp; omega⟩
      obtain ⟨i', hi'⟩ : ∃ i, k - (G.map (fun e => (e.capacity : ℝ)) ++
          (List.finRange n).map π').length = i + 1 := ⟨k - (G.length + n) - 1, by simp; omega⟩
      rw [hi, hi']
      have : i = i' := by simp at hi hi'; omega
      subst this
      simp
  · rfl

theorem rmem_graph_pi {n : ℕ} (G : Graph n) (π : Fin n → ℝ) (ps : List ℝ) (v : Fin n) :
    rmem (graphReals G π ps) ((G.length : ℤ) + ((v : ℕ) : ℤ)) = π v := by
  unfold rmem graphReals
  rw [if_pos (by positivity), show ((G.length : ℤ) + ((v : ℕ) : ℤ)).toNat = G.length + v by omega,
    List.getD_append _ _ _ _ (by simp), List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem rmem_graph_phi {n : ℕ} (G : Graph n) (π : Fin n → ℝ) (a b : ℝ) :
    rmem (graphReals G π [a, b]) ((G.length : ℤ) + n) = a := by
  unfold rmem graphReals
  rw [if_pos (by positivity), show ((G.length : ℤ) + (n : ℤ)).toNat = G.length + n by omega,
    List.getD_append_right _ _ _ _ (by simp)]
  simp

/-- The prologue: relocates the real input, saves the weights and `n`, perturbs the weights. -/
theorem prologue_spec (A : ℕ) (P : Program) {n : ℕ} (G : Graph n) (π : Fin n → ℝ) (ϕ κ : ℝ) :
    ∃ D : ℤ → ℝ, (∀ v : Fin n, D v = π v) ∧ D (-1) = n ∧ ∀ ω : Tape,
      Sim (scratch P) offs D (preWork n G.length)
        (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ)
        (run (fullProg A P) (instanceState G π ϕ κ) ω (preWork n G.length)) := by
  obtain ⟨m0, hm0⟩ : ∃ m0, m0 = rmem (graphReals G π [ϕ, κ]) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = (G.length : ℤ) + G.length := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = pertN A π := ⟨_, rfl⟩
  have hBe : 2 ∣ B := ⟨G.length, by rw [hB]; ring⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hneg : ∀ z, z < 0 → m0 z = 0 := fun z hz => by rw [hm0]; exact rmem_neg _ z hz
  have hm1 : ∀ z, copyMem m0 0 (2 * z) = m0 z := copyMem_even m0 hneg
  obtain ⟨mF, hmF⟩ : ∃ mF : ℤ → ℝ, mF = Function.update (Function.update (tr3 (copyMem m0 0) B N n)
      (B + 2 * (n : ℤ)) (tr3 (copyMem m0 0) B N n (B + 2 * (n : ℤ)) / N)) (-1) (n : ℝ) := ⟨_, rfl⟩
  have hD : ∀ v : Fin n, mF (2 * ((v : ℕ) : ℤ) + 1) = π v := by
    intro v
    have hv := v.isLt
    rw [hmF, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    unfold tr3
    rw [if_neg (by omega), if_pos (by omega),
      show B + (2 * ((v : ℕ) : ℤ) + 1) - 1 = 2 * ((G.length : ℤ) + ((v : ℕ) : ℤ)) by rw [hB]; ring,
      hm1, hm0, rmem_graph_pi]
  refine ⟨fun z => mF (2 * z + 1), hD, ?_, fun ω => ?_⟩
  · show mF (2 * (-1) + 1) = n
    rw [show (2 : ℤ) * (-1) + 1 = -1 by norm_num, hmF, Function.update_self]
  -- the run
  have hs : instanceState G π ϕ κ = mkS 0 (fun _ => 0) (fun _ => 0) m0
      (fun z => if 0 ≤ z then (graphInts G).getD z.toNat 0 else 0) 0 0 0 := by rw [hm0]; rfl
  obtain ⟨im0, him0⟩ : ∃ im0 : ℤ → ℤ,
      im0 = fun z => if 0 ≤ z then (graphInts G).getD z.toNat 0 else 0 := ⟨_, rfl⟩
  rw [← him0] at hs
  have him00 : im0 0 = n := by rw [him0]; simp [graphInts]
  have him01 : im0 1 = G.length := by rw [him0]; simp [graphInts]
  obtain ⟨p1, h1, a0, a1, a3, a4, a5, aq⟩ := pre_init A P ω (fun _ => 0) (fun _ => 0) m0 im0 0 0 0
  have hL : copyMem m0 ((G.length + n + 2 : ℕ) : ℤ) = m0 := by
    apply copyMem_full m0 _ (by positivity)
    intro z hz; rw [hm0]; apply rmem_large
    rw [graphReals_length]; push_cast at hz ⊢; omega
  obtain ⟨r2, p2, h2, b5, b0, b1, b3, b4, bq, br⟩ := pre_loop1 A P ω m0 im0 0 0
    (G.length + n + 2) (fun _ => 0) p1 (0 + 6)
    (by rw [a5, him00, him01]; push_cast; ring) a1
  rw [hL] at h2
  have h3 := pre_exit1 A P ω r2 p2 (copyMem m0 0) im0 0 (0 + 6 + 6 * (G.length + n + 2)) 0 b5
    (by rw [b1, a1])
  obtain ⟨r4, p4, h4, c1, c6, c2, c7, c5, c7', c0, c1', c3, c4, cq, cr⟩ := pre_mid1 A P ω r2 p2
    (copyMem m0 0) im0 0 (0 + 6 + 6 * (G.length + n + 2) + 1) 0
  obtain ⟨r5, p5, h5, d2, d1, d6, d7, d7', d0, d1', d3, d4, dq, dr⟩ := pre_loop2 A P ω
    (copyMem m0 0) im0 0 0 B n 0 r4 p4 (0 + 6 + 6 * (G.length + n + 2) + 1 + 12)
    (by rw [c7', b3, a3, him00]) (by rw [c0, b0, a0])
    (by rw [c5, b4, a4, him01, hB]; ring)
  have h6 := pre_exit2 A P ω r5 p5 (copyMem m0 0) im0 0
    (0 + 6 + 6 * (G.length + n + 2) + 1 + 12 + 8 * n) 0 d7' (by rw [d0, c0, b0, a0])
  obtain ⟨r7, p7, h7, g1, g6, g7, g5, g8, g7', g0, g1', gq, gr⟩ := pre_mid2 A P ω r5 p5
    (copyMem m0 0) im0 0 (0 + 6 + 6 * (G.length + n + 2) + 1 + 12 + 8 * n + 1) 0
  have hNr : r7 1 = N := by
    rw [g1, d1, d2, c1, c2, d6, c6, b3, a3, him00, hN]
    unfold pertN
    have hprod : (∏ i ∈ Finset.range n, (copyMem m0 0 (B + 2 * ((0 + i : ℕ) : ℤ)) /
        copyMem m0 0 (B + 2 * ((0 + i : ℕ) : ℤ)))) = ∏ v : Fin n, π v / π v := by
      rw [← Fin.prod_univ_eq_prod_range (fun i => copyMem m0 0 (B + 2 * ((0 + i : ℕ) : ℤ)) /
        copyMem m0 0 (B + 2 * ((0 + i : ℕ) : ℤ)))]
      refine Finset.prod_congr rfl (fun v _ => ?_)
      rw [show B + 2 * ((0 + (v : ℕ) : ℕ) : ℤ) = 2 * ((G.length : ℤ) + ((v : ℕ) : ℤ)) by
        rw [hB]; push_cast; ring, hm1, hm0, rmem_graph_pi]
    rw [hprod]; push_cast; ring
  obtain ⟨r8, p8, h8, k1, k7, k7', k0, k1', k5, kq, kr⟩ := pre_loop3 A P ω (copyMem m0 0) im0 0 0 B N
    hBe hB0 n 0 r7 p7 (0 + 6 + 6 * (G.length + n + 2) + 1 + 12 + 8 * n + 1 + 6)
    (by rw [g7', d3, c3, b3, a3, him00]) (by rw [g0, d0, c0, b0, a0])
    (by rw [g5, d4, c4, b4, a4, him01, hB]; ring) (by rw [g8]; ring) hNr (by rw [g6, d6, c6])
  have h9 := pre_exit3 A P ω r8 p8 (tr3 (copyMem m0 0) B N (0 + n)) im0 0
    (0 + 6 + 6 * (G.length + n + 2) + 1 + 12 + 8 * n + 1 + 6 + 14 * n) 0 k7'
    (by rw [k0, g0, d0, c0, b0, a0])
  obtain ⟨r10, p10, h10, lr, lp⟩ := pre_final A P ω r8 p8 (tr3 (copyMem m0 0) B N (0 + n)) im0 0
    (0 + 6 + 6 * (G.length + n + 2) + 1 + 12 + 8 * n + 1 + 6 + 14 * n + 1) 0
  have hp1 : p8 1 = -1 := by rw [k1', g1', d1', c1', b1, a1]
  have hr7 : r8 7 = n := by rw [k7, g7, d7, c7, b3, a3, him00]; norm_num
  rw [k5, hp1, k1, hNr, hr7, Nat.zero_add, ← hmF] at h10
  have hrun : run (fullProg A P) (instanceState G π ϕ κ) ω (preWork n G.length) =
      mkS offs r10 p10 mF im0 0 (0 + 6 + 6 * (G.length + n + 2) + 1 + 12 + 8 * n + 1 + 6 + 14 * n
        + 1 + 20) 0 := by
    rw [hs, show preWork n G.length = 6 + (6 * (G.length + n + 2) + (1 + (12 + (8 * n + (1 + (6 +
      (14 * n + (1 + 20)))))))) by unfold preWork; ring,
      run_add, h1, run_add, h2, run_add, h3, run_add, h4, run_add, h5, run_add, h6, run_add, h7,
      ← tr3_zero (copyMem m0 0) B N, run_add, h8, run_add, h9, show (0 + n : ℕ) = n from Nat.zero_add n, h10]
  rw [hrun]
  have hr0 : ∀ k, 9 ≤ k ∨ k = 4 ∨ k = 5 → r8 k = 0 := by
    intro k hk
    rw [kr k hk, gr k hk, dr k hk, cr k hk, br k (by omega)]
  have hp0 : ∀ q, q = 0 ∨ 9 ≤ q → p8 q = 0 := by
    intro q hq
    rcases hq with hq | hq
    · rw [hq, k0, g0, d0, c0, b0, a0]
    · rw [kq q hq, gq q hq, dq q hq, cq q hq, bq q hq, aq q hq]
  refine ⟨rfl, ?_, ?_, ?_, fun z => rfl, by rw [him0]; rfl, rfl, rfl, rfl, rfl, ?_⟩
  · show r10 = fun _ => 0
    funext k; rw [lr k]; split_ifs with hk
    · exact hr0 k hk
    · rfl
  · intro q _
    show p10 q = 0
    rw [lp q]; split_ifs with hq
    · exact hp0 q hq
    · rfl
  · intro z
    show mF (2 * z) = rmem (graphReals G (pertW (pertN A π) π) [ϕ / pertN A π, κ]) z
    rw [hmF, Function.update_of_ne (show 2 * z ≠ -1 by omega)]
    by_cases hz1 : z = (G.length : ℤ) + n
    · rw [hz1, show 2 * ((G.length : ℤ) + n) = B + 2 * (n : ℤ) by rw [hB]; ring,
        Function.update_self, tr3_at _ _ _ _ hBe,
        show B + 2 * (n : ℤ) = 2 * ((G.length : ℤ) + n) by rw [hB]; ring, hm1, hm0,
        rmem_graph_phi, rmem_graph_phi, hN]
    · rw [Function.update_of_ne (show 2 * z ≠ B + 2 * (n : ℤ) by rw [hB]; omega)]
      unfold tr3
      rw [if_neg (show ¬(¬ 2 ∣ 2 * z ∧ 1 ≤ 2 * z ∧ 2 * z < 2 * (n : ℤ)) by omega), hm1]
      by_cases hz2 : (G.length : ℤ) ≤ z ∧ z < G.length + n
      · rw [if_pos (show 2 ∣ 2 * z ∧ B ≤ 2 * z ∧ 2 * z < B + 2 * (n : ℤ) by rw [hB]; omega)]
        obtain ⟨v, hv⟩ : ∃ v : Fin n, z = (G.length : ℤ) + ((v : ℕ) : ℤ) :=
          ⟨⟨(z - G.length).toNat, by omega⟩, by simp; omega⟩
        rw [hv, hm0, rmem_graph_pi, rmem_graph_pi, hN]
        rfl
      · rw [if_neg (show ¬(2 ∣ 2 * z ∧ B ≤ 2 * z ∧ 2 * z < B + 2 * (n : ℤ)) by rw [hB]; omega),
          hm0]
        exact rmem_graph_out G π _ ϕ _ κ z (by omega)
  · show 0 + 6 + 6 * (G.length + n + 2) + 1 + 12 + 8 * n + 1 + 6 + 14 * n + 1 + 20 =
      preWork n G.length + 2 * 0
    unfold preWork; ring


/-! ## Post-processing -/

theorem post_init (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    ∃ r' p', run (fullProg A P) (mkS 72 r p m im c w g) ω 8 = mkS 80 r' p' m im c (w + 8) g ∧
      r' 11 = m (-1) ∧ r' 6 = 1 ∧ r' 9 = 0 ∧ r' 10 = 0 ∧ p' 0 = 0 ∧ p' 1 = -1 ∧ p' 8 = 1 ∧
      p' 9 = -1 := by
  simp only [run_front, run_zero, stp72, stp73, stp74, stp75, stp76, stp77, stp78, stp79]
  exact ⟨_, _, rfl, by simp [Function.update_apply]⟩

theorem post_iter1 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) (hRC : ¬ r 11 ≤ 0) :
    ∃ r' p', run (fullProg A P) (mkS 80 r p m im c w g) ω 15 = mkS 80 r' p' m im c (w + 15) g ∧
      r' 11 = r 11 - r 6 ∧ r' 6 = r 6 ∧
      r' 9 = r 9 + m (p 8) * (((im (p 9) : ℤ) : ℝ) / ((im (p 9) : ℤ) : ℝ)) ∧
      r' 10 = r 10 + m (p 8) * (r 6 - ((im (p 9) : ℤ) : ℝ) / ((im (p 9) : ℤ) : ℝ)) ∧
      p' 0 = p 0 ∧ p' 1 = p 1 ∧ p' 8 = p 8 + 1 + 1 ∧ p' 9 = p 9 - 1 := by
  simp only [run_front, run_zero, stp80, hRC, if_false, stp81, stp82, stp83, stp84, stp85, stp86, stp87, stp88, stp89, stp90, stp91, stp92, stp93, stp94]
  exact ⟨_, _, rfl, by simp [Function.update_apply]⟩

/-- The real value of the label of vertex `v`. -/
noncomputable def lab (im : ℤ → ℤ) (v : ℕ) : ℝ := ((im (-1 - (v : ℤ)) : ℤ) : ℝ)
/-- Contribution of vertex `v` to `π(S)`. -/
noncomputable def sA (m : ℤ → ℝ) (im : ℤ → ℤ) (v : ℕ) : ℝ :=
  m (2 * (v : ℤ) + 1) * (lab im v / lab im v)
/-- Contribution of vertex `v` to `π(Sᶜ)`. -/
noncomputable def sB (m : ℤ → ℝ) (im : ℤ → ℤ) (v : ℕ) : ℝ :=
  m (2 * (v : ℤ) + 1) * (1 - lab im v / lab im v)

theorem post_loop1 (A : ℕ) (P : Program) (ω : Tape) (m : ℤ → ℝ) (im : ℤ → ℤ) (c g : ℕ) :
    ∀ j k : ℕ, ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (w : ℕ), r 11 = j → r 6 = 1 →
      p 8 = 2 * (k : ℤ) + 1 → p 9 = -1 - (k : ℤ) →
      ∃ r' p', run (fullProg A P) (mkS 80 r p m im c w g) ω (15 * j) =
          mkS 80 r' p' m im c (w + 15 * j) g ∧
        r' 11 = 0 ∧ r' 6 = 1 ∧ p' 0 = p 0 ∧ p' 1 = p 1 ∧
        r' 9 = r 9 + ∑ i ∈ Finset.range j, sA m im (k + i) ∧
        r' 10 = r 10 + ∑ i ∈ Finset.range j, sB m im (k + i) := by
  intro j
  induction j with
  | zero =>
    intro k r p w h11 h6 _ _
    exact ⟨r, p, rfl, by simpa using h11, h6, rfl, rfl, by simp, by simp⟩
  | succ j ih =>
    intro k r p w h11 h6 h8 h9
    have hRC : ¬ r 11 ≤ 0 := by
      rw [h11]; push_cast; have : (0:ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    obtain ⟨r1, p1, hrun1, e11, e6, e9, e10, e0, e1, e8, e9'⟩ :=
      post_iter1 A P ω r p m im c w g hRC
    obtain ⟨r', p', hrun, f11, f6, f0, f1, f9, f10⟩ := ih (k + 1) r1 p1 (w + 15)
      (by rw [e11, h11, h6]; push_cast; ring) (by rw [e6, h6])
      (by rw [e8, h8]; push_cast; ring) (by rw [e9', h9]; push_cast; ring)
    refine ⟨r', p', ?_, f11, f6, by rw [f0, e0], by rw [f1, e1], ?_, ?_⟩
    · rw [show 15 * (j + 1) = 15 + 15 * j by ring, run_add, hrun1, hrun]
      congr 1; omega
    · have hA : m (p 8) * (((im (p 9) : ℤ) : ℝ) / ((im (p 9) : ℤ) : ℝ)) = sA m im k := by
        rw [h8, h9]; rfl
      have h2 : ∑ i ∈ Finset.range j, sA m im (k + 1 + i) =
          ∑ i ∈ Finset.range j, sA m im (k + (i + 1)) :=
        Finset.sum_congr rfl (fun i _ => by rw [show k + 1 + i = k + (i + 1) by ring])
      rw [f9, e9, hA, Finset.sum_range_succ', h2, Nat.add_zero]; ring
    · have hB : m (p 8) * (r 6 - ((im (p 9) : ℤ) : ℝ) / ((im (p 9) : ℤ) : ℝ)) = sB m im k := by
        rw [h8, h9, h6]; rfl
      have h2 : ∑ i ∈ Finset.range j, sB m im (k + 1 + i) =
          ∑ i ∈ Finset.range j, sB m im (k + (i + 1)) :=
        Finset.sum_congr rfl (fun i _ => by rw [show k + 1 + i = k + (i + 1) by ring])
      rw [f10, e10, hB, Finset.sum_range_succ', h2, Nat.add_zero]; ring

theorem post_exit1 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) (h : r 11 = 0) :
    run (fullProg A P) (mkS 80 r p m im c w g) ω 1 = mkS 95 r p m im c (w + 1) g := by
  simp only [run_front, run_zero, stp80, h, le_refl, if_true]

theorem post_decide (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    ∃ r' p', run (fullProg A P) (mkS 95 r p m im c w g) ω 6 = mkS 108 r' p' m im c (w + 6) g ∧
      r' 6 = r 6 ∧ p' 0 = p 0 ∧ p' 1 = p 1 ∧
      p' 11 = (if r 9 ≤ 0 then 0 else if r 9 - r 10 ≤ 0 then 1 else 0) ∧
      p' 12 = (if r 9 ≤ 0 then 0 else if r 9 - r 10 ≤ 0 then 0 else 1) := by
  by_cases h1 : r 9 ≤ 0
  · simp only [run_front, run_zero, stp95, stp96, Function.update_of_ne (show (9:ℕ) ≠ 0 by decide),
      h1, if_true, stp104, stp105, stp106, stp107]
    exact ⟨_, _, rfl, by simp [Function.update_apply, h1]⟩
  · by_cases h2 : r 9 - r 10 ≤ 0
    · simp only [run_front, run_zero, stp95, stp96,
        Function.update_of_ne (show (9:ℕ) ≠ 0 by decide),
        h1, if_false, stp97, Function.update_self, h2, if_true, stp101, stp102, stp103]
      exact ⟨_, _, rfl, by simp [Function.update_apply, h1, h2]⟩
    · simp only [run_front, run_zero, stp95, stp96,
        Function.update_of_ne (show (9:ℕ) ≠ 0 by decide),
        h1, if_false, stp97, Function.update_self, h2, stp98, stp99, stp100]
      exact ⟨_, _, rfl, by simp [Function.update_apply, h1, h2]⟩

theorem post_mid (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) :
    ∃ r' p', run (fullProg A P) (mkS 108 r p m im c w g) ω 2 = mkS 110 r' p' m im c (w + 2) g ∧
      r' 11 = m (p 1) ∧ r' 6 = r 6 ∧ p' 0 = p 0 ∧ p' 9 = -1 ∧ p' 11 = p 11 ∧ p' 12 = p 12 := by
  simp only [run_front, run_zero, stp108, stp109]
  exact ⟨_, _, rfl, by simp [Function.update_apply]⟩

theorem post_iter2 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) (hRC : ¬ r 11 ≤ 0) (hp0 : p 0 = 0) :
    ∃ r' p' im', run (fullProg A P) (mkS 110 r p m im c w g) ω 10 =
        mkS 110 r' p' m im' c (w + 10) g ∧
      im' = Function.update im (p 9) (if im (p 9) = 0 then p 12 else p 11) ∧
      r' 11 = r 11 - r 6 ∧ r' 6 = r 6 ∧ p' 0 = p 0 ∧ p' 9 = p 9 - 1 ∧ p' 11 = p 11 ∧
      p' 12 = p 12 := by
  rcases lt_trichotomy (im (p 9)) 0 with h | h | h
  · simp only [run_front, run_zero, stp110, hRC, if_false, stp111, stp112, Function.update_self,
      Function.update_of_ne (show (0:ℕ) ≠ 13 by decide), hp0, h.le, if_true, stp116,
      not_le.2 h, stp117, stp118, stp121, stp122, stp123, stp124]
    exact ⟨_, _, _, rfl, by simp [Function.update_apply, h.ne], by simp [Function.update_apply, hp0]⟩
  · simp only [run_front, run_zero, stp110, hRC, if_false, stp111, stp112, Function.update_self,
      Function.update_of_ne (show (0:ℕ) ≠ 13 by decide), hp0, h, le_refl, if_true, stp116,
      stp119, stp120, stp121, stp122, stp123, stp124]
    exact ⟨_, _, _, rfl, by simp [Function.update_apply, h], by simp [Function.update_apply, hp0]⟩
  · simp only [run_front, run_zero, stp110, hRC, if_false, stp111, stp112, Function.update_self,
      Function.update_of_ne (show (0:ℕ) ≠ 13 by decide), hp0, not_le.2 h,
      stp113, stp114, stp115, stp121, stp122, stp123, stp124]
    exact ⟨_, _, _, rfl, by simp [Function.update_apply, h.ne'], by simp [Function.update_apply, hp0]⟩

/-- The label written for a vertex with old label `l`. -/
def outv (pa pb l : ℤ) : ℤ := if l = 0 then pb else pa

theorem post_loop2 (A : ℕ) (P : Program) (ω : Tape) (m : ℤ → ℝ) (c g : ℕ) (pa pb : ℤ) :
    ∀ j k : ℕ, ∀ (r : ℕ → ℝ) (p : ℕ → ℤ) (im : ℤ → ℤ) (w : ℕ), r 11 = j → r 6 = 1 → p 0 = 0 →
      p 9 = -1 - (k : ℤ) → p 11 = pa → p 12 = pb →
      ∃ r' p' im', run (fullProg A P) (mkS 110 r p m im c w g) ω (10 * j) =
          mkS 110 r' p' m im' c (w + 10 * j) g ∧ r' 11 = 0 ∧
        ∀ v : ℕ, im' (-1 - (v : ℤ)) =
          if k ≤ v ∧ v < k + j then outv pa pb (im (-1 - (v : ℤ))) else im (-1 - (v : ℤ)) := by
  intro j
  induction j with
  | zero =>
    intro k r p im w h11 _ _ _ _ _
    refine ⟨r, p, im, rfl, by simpa using h11, fun v => ?_⟩
    rw [if_neg (show ¬(k ≤ v ∧ v < k + 0) by omega)]
  | succ j ih =>
    intro k r p im w h11 h6 h0 h9 h11' h12
    have hRC : ¬ r 11 ≤ 0 := by
      rw [h11]; push_cast; have : (0:ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    obtain ⟨r1, p1, im1, hrun1, eim, e11, e6, e0, e9, e11', e12⟩ :=
      post_iter2 A P ω r p m im c w g hRC h0
    obtain ⟨r', p', im', hrun, f11, fim⟩ := ih (k + 1) r1 p1 im1 (w + 10)
      (by rw [e11, h11, h6]; push_cast; ring) (by rw [e6, h6]) (by rw [e0, h0])
      (by rw [e9, h9]; push_cast; ring) (by rw [e11', h11']) (by rw [e12, h12])
    refine ⟨r', p', im', ?_, f11, fun v => ?_⟩
    · rw [show 10 * (j + 1) = 10 + 10 * j by ring, run_add, hrun1, hrun]
      congr 1; omega
    · rw [fim v, eim, h9, h11', h12]
      by_cases hv : v = k
      · rw [hv, if_neg (show ¬(k + 1 ≤ k ∧ k < k + 1 + j) by omega),
          if_pos (show k ≤ k ∧ k < k + (j + 1) by omega), Function.update_self]
        rfl
      · rw [Function.update_of_ne (show (-1 - (v : ℤ)) ≠ -1 - (k : ℤ) by omega)]
        split_ifs <;> first | rfl | omega

theorem post_exit2 (A : ℕ) (P : Program) (ω : Tape) (r : ℕ → ℝ) (p : ℕ → ℤ) (m : ℤ → ℝ)
    (im : ℤ → ℤ) (c w g : ℕ) (h : r 11 = 0) :
    run (fullProg A P) (mkS 110 r p m im c w g) ω 2 = ⟨⟨⟨126, r, p, m⟩, im, c, true, w + 1 + 1⟩, g⟩ := by
  simp only [run_front, run_zero, stp110, h, le_refl, if_true, stp125]

theorem sum_sAB {n : ℕ} (π : Fin n → ℝ) (m : ℤ → ℝ) (im : ℤ → ℤ)
    (hπ : ∀ v : Fin n, m (2 * (v : ℤ) + 1) = π v) :
    ∑ i ∈ Finset.range n, sA m im (0 + i) =
        mass π (univ.filter (fun v : Fin n => im (-1 - ((v : ℕ) : ℤ)) ≠ 0)) ∧
    ∑ i ∈ Finset.range n, sB m im (0 + i) =
        mass π (univ.filter (fun v : Fin n => im (-1 - ((v : ℕ) : ℤ)) ≠ 0))ᶜ := by
  simp only [Nat.zero_add]
  constructor
  · rw [← Fin.sum_univ_eq_sum_range (sA m im), mass, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    unfold sA lab; rw [hπ v]
    by_cases h : im (-1 - ((v : ℕ) : ℤ)) = 0
    · simp [h]
    · have : ((im (-1 - ((v : ℕ) : ℤ)) : ℤ) : ℝ) ≠ 0 := by exact_mod_cast h
      simp [h, div_self this]
  · rw [← Fin.sum_univ_eq_sum_range (sB m im), mass, Finset.compl_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    unfold sB lab; rw [hπ v]
    by_cases h : im (-1 - ((v : ℕ) : ℤ)) = 0
    · simp [h]
    · have : ((im (-1 - ((v : ℕ) : ℤ)) : ℤ) : ℝ) ≠ 0 := by exact_mod_cast h
      simp [h, div_self this]

theorem eq_mkS (σ : State) (hh : σ.base.halted = false) :
    σ = mkS σ.base.core.pc σ.base.core.regs σ.base.core.ptrs σ.base.core.mem
      σ.base.integerMemory σ.base.cursor σ.base.work σ.gaussianCursor := by
  obtain ⟨⟨⟨pc, r, p, m⟩, im, c, hl, w⟩, g⟩ := σ
  simp only at hh; subst hh; rfl

theorem post_spec (A : ℕ) (P : Program) {n : ℕ} (π : Fin n → ℝ) (σ : State) (ω : Tape)
    (hpc : σ.base.core.pc = postStart) (hh : σ.base.halted = false)
    (hπ : ∀ v : Fin n, σ.base.core.mem (2 * (v : ℤ) + 1) = π v)
    (hn : σ.base.core.mem (-1) = n) :
    (run (fullProg A P) σ ω (postWork n)).base.halted = true ∧
    (run (fullProg A P) σ ω (postWork n)).base.work = σ.base.work + postWork n ∧
    outputCut n (run (fullProg A P) σ ω (postWork n)) = postOut π (outputCut n σ) := by
  obtain ⟨⟨⟨pc, r0, p0, m⟩, im, c, hl, w⟩, g⟩ := σ
  simp only at hpc hh hπ hn
  subst hpc hh
  obtain ⟨r1, p1, h1, a11, a6, a9, a10, a0, a1, a8, a9'⟩ := post_init A P ω r0 p0 m im c w g
  obtain ⟨r2, p2, h2, b11, b6, b0, b1, b9, b10⟩ := post_loop1 A P ω m im c g n 0 r1 p1 (w + 8)
    (by rw [a11, hn]) a6 (by rw [a8]; norm_num) (by rw [a9']; norm_num)
  have h3 := post_exit1 A P ω r2 p2 m im c (w + 8 + 15 * n) g b11
  obtain ⟨r4, p4, h4, d6, d0, d1, d11, d12⟩ := post_decide A P ω r2 p2 m im c (w + 8 + 15 * n + 1) g
  obtain ⟨r5, p5, h5, e11, e6, e0, e9, e11', e12⟩ := post_mid A P ω r4 p4 m im c
    (w + 8 + 15 * n + 1 + 6) g
  obtain ⟨r6, p6, im6, h6, f11, fim⟩ := post_loop2 A P ω m c g (p4 11) (p4 12) n 0 r5 p5 im
    (w + 8 + 15 * n + 1 + 6 + 2) (by rw [e11, d1, b1, a1, hn]) (by rw [e6, d6, b6])
    (by rw [e0, d0, b0, a0]) (by rw [e9]; norm_num) e11' e12
  have h7 := post_exit2 A P ω r6 p6 m im6 c (w + 8 + 15 * n + 1 + 6 + 2 + 10 * n) g f11
  have hrun : run (fullProg A P) (mkS 72 r0 p0 m im c w g) ω (postWork n) =
      ⟨⟨⟨126, r6, p6, m⟩, im6, c, true, w + 8 + 15 * n + 1 + 6 + 2 + 10 * n + 1 + 1⟩, g⟩ := by
    rw [show postWork n = 8 + (15 * n + (1 + (6 + (2 + (10 * n + 2))))) by unfold postWork; ring,
      run_add, h1, run_add, h2, run_add, h3, run_add, h4, run_add, h5, run_add, h6, h7]
  change (run (fullProg A P) (mkS 72 r0 p0 m im c w g) ω (postWork n)).base.halted = true ∧
    (run (fullProg A P) (mkS 72 r0 p0 m im c w g) ω (postWork n)).base.work = w + postWork n ∧
    outputCut n (run (fullProg A P) (mkS 72 r0 p0 m im c w g) ω (postWork n)) =
      postOut π (outputCut n (mkS 72 r0 p0 m im c w g))
  rw [hrun]
  refine ⟨rfl, by simp only [postWork]; ring, ?_⟩
  obtain ⟨hsA, hsB⟩ := sum_sAB π m im hπ
  rw [b9, a9, zero_add, hsA, b10, a10, zero_add, hsB] at d11 d12
  rw [show outputCut n (mkS 72 r0 p0 m im c w g) =
    univ.filter (fun v : Fin n => im (-1 - ((v : ℕ) : ℤ)) ≠ 0) from rfl]
  ext v
  have hv := fim v.val
  rw [if_pos (show 0 ≤ v.val ∧ v.val < 0 + n by omega)] at hv
  unfold postOut
  by_cases q1 : mass π (univ.filter (fun v : Fin n => im (-1 - ((v : ℕ) : ℤ)) ≠ 0)) ≤ 0 <;>
  by_cases q2 : mass π (univ.filter (fun v : Fin n => im (-1 - ((v : ℕ) : ℤ)) ≠ 0)) -
    mass π (univ.filter (fun v : Fin n => im (-1 - ((v : ℕ) : ℤ)) ≠ 0))ᶜ ≤ 0 <;>
  simp only [q1, q2, if_true, if_false] at d11 d12 ⊢ <;>
  by_cases hl : im (-1 - ((v : ℕ) : ℤ)) = 0 <;>
  simp_all [outv, outputCut, ClusterDecomp.label, Finset.mem_filter, Finset.mem_compl]

theorem machine_reduction (P : Program) (hP : Admissible P) (A : ℕ) :
    ∃ P' : Program, Admissible P' ∧ ∃ K : ℕ, ∀ (n : ℕ) (G : Graph n) (π : Fin n → ℝ) (ϕ κ : ℝ),
      2 ≤ n →
      ∃ W : ℕ, (W : ℝ) ≤ K * ((n : ℝ) + G.length + 1) ∧
        (∀ ω, Halts P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω →
          Halts P' (instanceState G π ϕ κ) ω ∧
          (final P' (instanceState G π ϕ κ) ω).base.work =
            2 * (final P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω).base.work
              + W ∧
          outputCut n (final P' (instanceState G π ϕ κ) ω) =
            postOut π (outputCut n
              (final P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω))) ∧
        (∀ ω t, (run P' (instanceState G π ϕ κ) ω t).base.halted = true →
          Halts P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω) := by
  classical
  refine ⟨fullProg A P, fullProg_admissible A P hP, 77, ?_⟩
  intro n G π ϕ κ _
  obtain ⟨D, hD, hD1, hS0⟩ := prologue_spec A P G π ϕ κ
  have hsim : ∀ ω j,
      (run P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω j).base.halted = false →
      Sim (scratch P) offs D (preWork n G.length)
        (run P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω j)
        (run (fullProg A P) (instanceState G π ϕ κ) ω (preWork n G.length + 2 * j)) := by
    intro ω j
    induction j with
    | zero => intro _; exact hS0 ω
    | succ j ih =>
      intro hj
      have hS := ih (not_halted_of_succ _ _ _ j hj)
      have hne : P[(run P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω j).base.core.pc]?
          ≠ some (.base .halt) := by
        intro heq
        have := ((sim_step A P hP D _ ω _ _ hS).2 heq).1
        rw [← run_succ] at this; rw [this] at hj; cases hj
      have := (sim_step A P hP D _ ω _ _ hS).1 hne
      rw [run_succ, show preWork n G.length + 2 * (j + 1) = (preWork n G.length + 2 * j) + 2 by ring,
        run_add]
      exact this
  refine ⟨preWork n G.length + postWork n - 1, ?_, ?_, ?_⟩
  · have : preWork n G.length + postWork n - 1 ≤ 77 * (n + G.length + 1) := by
      simp only [preWork, postWork]; omega
    exact_mod_cast this
  · intro ω hH
    obtain ⟨h, hfin, hh, hmin⟩ : ∃ h,
        final P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω =
          run P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω h ∧
        (run P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω h).base.halted = true ∧
        ∀ j < h,
          (run P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω j).base.halted = false := by
      refine ⟨haltTime P _ ω, rfl, final_halted _ _ ω hH, fun j hj => ?_⟩
      have hj' : j < Nat.find hH := by unfold haltTime at hj; rw [dif_pos hH] at hj; exact hj
      have := Nat.find_min hH hj'
      simpa using this
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := by
      cases h with
      | zero => rw [show run P _ ω 0 = _ from rfl] at hh; cases hh
      | succ k => exact ⟨k, rfl⟩
    have hSk := hsim ω k (hmin k (by omega))
    have heq : P[(run P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω k).base.core.pc]?
        = some (.base .halt) := by
      by_contra hne
      have := ((sim_step A P hP D _ ω _ _ hSk).1 hne).halted
      rw [← run_succ, hh] at this; cases this
    obtain ⟨-, hsw, hsi, hσpc, hσh, hσw, hσm, hσi⟩ := (sim_step A P hP D _ ω _ _ hSk).2 heq
    rw [← run_add] at hσpc hσh hσw hσm hσi
    obtain ⟨hp1, hp2, hp3⟩ := post_spec A P π
      (run (fullProg A P) (instanceState G π ϕ κ) ω (preWork n G.length + 2 * k + 1)) ω hσpc hσh
      (by intro v; rw [hσm, hSk.memO, hD])
      (by rw [hσm, show (-1 : ℤ) = 2 * (-1) + 1 by norm_num, hSk.memO, hD1])
    rw [← run_add] at hp1 hp2 hp3
    have hfin' := final_eq_of_halted _ _ ω _ hp1
    refine ⟨⟨_, hp1⟩, ?_, ?_⟩
    · rw [hfin', hp2, hσw, hSk.work, hfin, run_succ, hsw]
      simp only [preWork, postWork]; omega
    · rw [hfin', hp3, hfin]
      congr 1
      apply outputCut_congr
      rw [hσi, hSk.imem, run_succ, hsi]
  · intro ω t ht
    by_contra hH
    have hnh : ∀ j,
        (run P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω j).base.halted = false := by
      intro j
      cases hj : (run P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω j).base.halted
      · rfl
      · exact absurd ⟨j, hj⟩ hH
    have hS := (hsim ω t (hnh t)).halted'
    have hst := run_halted_stable _ _ ω t ht (preWork n G.length + t)
    rw [show t + (preWork n G.length + t) = preWork n G.length + 2 * t by ring] at hst
    rw [hst, ht] at hS
    cases hS

/-! ## Assembly -/

instance tapeLaw_isProb : MeasureTheory.IsProbabilityMeasure tapeLaw := by
  unfold tapeLaw ClusterDecomp.coinTape; infer_instance

theorem zero_weights_reduction_proof : BalancedOracle true → BalancedOracle false := by
  rintro ⟨c₁, c₂, cβ, Cq, hc₁, hc₂, hβ, hq, H⟩
  refine ⟨c₁, c₂, min (cβ / 2) (1 / 200), 4 * Cq, hc₁, hc₂,
    lt_min (by linarith) (by norm_num), by linarith, ?_⟩
  intro a
  obtain ⟨P, hP, c, HP⟩ := H a
  obtain ⟨A, hA, hA1⟩ : ∃ A : ℕ, 2 / cβ ≤ (A : ℝ) ∧ 1 ≤ A :=
    ⟨⌈2 / cβ⌉₊ + 1, by push_cast; linarith [Nat.le_ceil (2 / cβ)], by omega⟩
  obtain ⟨P', hP', K, HM⟩ := machine_reduction P hP A
  refine ⟨P', hP', c, ?_⟩
  intro d
  obtain ⟨C, hC, HC⟩ := HP (d + 6 + A)
  refine ⟨2 * C + 2 * K * 2 ^ c, by positivity, ?_⟩
  intro n G π ϕ κ hn hloops hconn hunit hnorm _ htot hϕ hκ1 hκ2
  obtain ⟨hNpos, hZ1, hZ2, hnorm', hpos', htot'⟩ := pert_props hn π hnorm d A cβ hβ hA hA1 htot
  have hϕ' : 0 < ϕ / pertN A π := div_pos hϕ hNpos
  obtain ⟨hB, hE, hH⟩ := HC n G (pertW (pertN A π) π) (ϕ / pertN A π) κ hn hloops hconn hunit
    hnorm' (fun _ => hpos') htot' hϕ' hκ1 hκ2
  obtain ⟨W, hW, Hfwd, Hhalt⟩ := HM n G π ϕ κ hn
  obtain ⟨hlogpos, hlog2, -⟩ := log_bounds hn
  have hT1 : 1 ≤ totalWeight π := by
    obtain ⟨v, hv⟩ := hnorm.2.1
    rw [← hv]; exact Finset.single_le_sum (fun w _ => hnorm.1 w) (Finset.mem_univ v)
  refine ⟨?_, ?_, ?_⟩
  · intro ω t ht
    show mass π (outputCut n (run P' (instanceState G π ϕ κ) ω t)) ≤
      mass π (outputCut n (run P' (instanceState G π ϕ κ) ω t))ᶜ
    rw [← final_eq_of_halted _ _ _ _ ht, (Hfwd ω (Hhalt ω t ht)).2.2]
    exact postOut_balanced π hnorm.1 _
  · obtain ⟨hae, hint, hle⟩ := hE
    have hae' : ∀ᵐ ω ∂tapeLaw, work P' (instanceState G π ϕ κ) ω =
        2 * work P (instanceState G (pertW (pertN A π) π) (ϕ / pertN A π) κ) ω + W := by
      filter_upwards [hae] with ω hω
      rw [work_of_halts _ _ _ (Hfwd ω hω).1, work_of_halts _ _ _ hω, (Hfwd ω hω).2.1]
      push_cast; ring
    have hint2 := (hint.const_mul 2).add (MeasureTheory.integrable_const (μ := tapeLaw) (W : ℝ))
    refine ⟨?_, hint2.congr (hae'.mono fun ω h => h.symm), ?_⟩
    · filter_upwards [hae] with ω hω using (Hfwd ω hω).1
    · rw [MeasureTheory.integral_congr_ae hae', MeasureTheory.integral_add (hint.const_mul 2)
        (MeasureTheory.integrable_const _), MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const]
      simp only [MeasureTheory.probReal_univ, one_smul]
      have hκ : 0 < κ := lt_of_lt_of_le (div_pos hc₁ hlogpos) hκ1
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have ha : (n : ℝ) + G.length ≤ (G.length : ℝ) + (n : ℝ) ^ (1 + κ) := by
        have : (n : ℝ) ≤ (n : ℝ) ^ (1 + κ) := by
          calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        linarith
      have hb : 1 ≤ 1 + Real.log G.total := by
        rcases total_zero_or_ge_one G hunit with h | h
        · rw [h, Real.log_zero]; norm_num
        · linarith [Real.log_nonneg h]
      have hc' : 1 ≤ 2 ^ c * Real.log n ^ c := by
        rw [← mul_pow]; exact one_le_pow₀ (by linarith)
      have hK : (0:ℝ) ≤ K := Nat.cast_nonneg _
      have hm0 : (0:ℝ) ≤ G.length := Nat.cast_nonneg _
      have hX : (W : ℝ) ≤ 2 * K * 2 ^ c * ((G.length : ℝ) + (n : ℝ) ^ (1 + κ)) *
          (1 + Real.log G.total) * Real.log n ^ c := by
        have e : 2 * K * 2 ^ c * ((G.length : ℝ) + (n : ℝ) ^ (1 + κ)) *
            (1 + Real.log G.total) * Real.log n ^ c =
            (2 * K * ((G.length : ℝ) + (n : ℝ) ^ (1 + κ))) *
              ((1 + Real.log G.total) * (2 ^ c * Real.log n ^ c)) := by ring
        rw [e]
        have h1 : (W : ℝ) ≤ 2 * K * ((G.length : ℝ) + (n : ℝ) ^ (1 + κ)) := by
          nlinarith [mul_le_mul_of_nonneg_left
            (show (n : ℝ) + G.length + 1 ≤ 2 * ((G.length : ℝ) + (n : ℝ) ^ (1 + κ)) by linarith) hK]
        have h2 : 1 ≤ (1 + Real.log G.total) * (2 ^ c * Real.log n ^ c) :=
          one_le_mul_of_one_le_of_one_le hb hc'
        have h3 : 0 ≤ 2 * K * ((G.length : ℝ) + (n : ℝ) ^ (1 + κ)) := by positivity
        nlinarith
      have e2 : (2 * C + 2 * K * 2 ^ c) * ((G.length : ℝ) + (n : ℝ) ^ (1 + κ)) *
          (1 + Real.log G.total) * Real.log n ^ c =
          2 * (C * ((G.length : ℝ) + (n : ℝ) ^ (1 + κ)) * (1 + Real.log G.total) * Real.log n ^ c) +
          2 * K * 2 ^ c * ((G.length : ℝ) + (n : ℝ) ^ (1 + κ)) *
            (1 + Real.log G.total) * Real.log n ^ c := by ring
      rw [e2]
      linarith
  · obtain ⟨E, hEm, hEp, hEg⟩ := hH
    refine ⟨E, hEm, hEp, fun ω hω => ?_⟩
    obtain ⟨hh, hg⟩ := hEg ω hω
    obtain ⟨hh', -, hout⟩ := Hfwd ω hh
    refine ⟨hh', ?_⟩
    show GoodCut G π ϕ κ (min (cβ / 2) (1 / 200)) (4 * Cq) (outputCut n (final P' (instanceState G π ϕ κ) ω))
    rw [hout]
    have hbal := hB ω _ (final_halted _ _ ω hh)
    exact goodcut_transfer hn G π ϕ κ cβ Cq _ hϕ hβ hq hNpos hnorm.1 hnorm.2.2 hT1 hZ1 hZ2 _
      hbal hg

end SparsestCutOracle.Main

theorem solution :
    SparsestCutOracle.Main.BalancedOracle true → SparsestCutOracle.Main.BalancedOracle false :=
  SparsestCutOracle.Main.zero_weights_reduction_proof
