-- Prove2me | solution 1 for SmoothCCP.Feasibility.theorem_3_13
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T19:05:03.728371+00:00
-- url     : https://prove2.me/submissions/84cbacc8-ee98-4c61-940e-7acf424fe39c

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting
open MeasureTheory

namespace RRAux_SmoothCCP_Feasibility_theorem_3_13

lemma gam_mem {ε : ℝ} {γ : ℝ → ℝ} (hγ : SmoothCCP.Feasibility.AdmissibleGamma ε γ) (y : ℝ) :
    SmoothCCP.Feasibility.Gam ε γ y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold SmoothCCP.Feasibility.Gam
  split_ifs with h1 h2
  · exact ⟨zero_le_one, le_rfl⟩
  · exact hγ.mapsTo y ⟨(not_le.mp h1).le, h2.le⟩
  · exact ⟨le_rfl, zero_le_one⟩

lemma gam_anti {ε : ℝ} {γ : ℝ → ℝ} (hγ : SmoothCCP.Feasibility.AdmissibleGamma ε γ) {y1 y2 : ℝ}
    (h : y1 ≤ y2) : SmoothCCP.Feasibility.Gam ε γ y2 ≤ SmoothCCP.Feasibility.Gam ε γ y1 := by
  have hm1 := gam_mem hγ y1
  have hm2 := gam_mem hγ y2
  unfold SmoothCCP.Feasibility.Gam at hm1 hm2 ⊢
  by_cases a2 : y2 ≤ -ε
  · have a1 : y1 ≤ -ε := h.trans a2
    simp [a1, a2]
  · by_cases b2 : y2 < ε
    · rw [if_neg a2, if_pos b2]
      by_cases a1 : y1 ≤ -ε
      · rw [if_pos a1]; rw [if_neg a2, if_pos b2] at hm2; exact hm2.2
      · rw [if_neg a1, if_pos (lt_of_le_of_lt h b2)]
        exact hγ.strictAnti.antitoneOn ⟨(not_le.mp a1).le, (lt_of_le_of_lt h b2).le⟩
          ⟨(not_le.mp a2).le, b2.le⟩ h
    · rw [if_neg a2, if_neg b2]; exact hm1.1

lemma gam_meas {ε : ℝ} {γ : ℝ → ℝ} (hγ : SmoothCCP.Feasibility.AdmissibleGamma ε γ) :
    Measurable (SmoothCCP.Feasibility.Gam ε γ) :=
  hγ.differentiable.continuous.measurable

/-- floor-cell index in one coordinate -/
lemma cell_bounds (K : ℕ) (hK : 1 ≤ K) (u : ℝ) (hu0 : 0 ≤ u) (huK : u ≤ K) :
    ((min ⌊u⌋₊ (K - 1) : ℕ) : ℝ) ≤ u ∧ u ≤ ((min ⌊u⌋₊ (K - 1) : ℕ) : ℝ) + 1 := by
  constructor
  · calc ((min ⌊u⌋₊ (K - 1) : ℕ) : ℝ) ≤ (⌊u⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
      _ ≤ u := Nat.floor_le hu0
  · by_cases h : ⌊u⌋₊ ≤ K - 1
    · rw [min_eq_left h]; exact (Nat.lt_floor_add_one u).le
    · rw [min_eq_right (not_le.mp h).le]
      have : ((K - 1 : ℕ) : ℝ) + 1 = K := by
        rw [Nat.cast_sub hK]; simp
      rw [this]; exact huK

lemma same_cell (K : ℕ) (hK : 1 ≤ K) (u v : ℝ) (hu0 : 0 ≤ u) (huK : u ≤ K) (hv0 : 0 ≤ v)
    (hvK : v ≤ K) (h : min ⌊u⌋₊ (K - 1) = min ⌊v⌋₊ (K - 1)) : |u - v| ≤ 1 := by
  have h1 := cell_bounds K hK u hu0 huK
  have h2 := cell_bounds K hK v hv0 hvK
  rw [h] at h1
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

lemma grid {n : ℕ} (X : Set (Fin n → ℝ)) (x0 : Fin n → ℝ) (hx0 : x0 ∈ X) (D : ℝ) (hD : 0 < D)
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ D) (s : ℝ) (hs : 0 < s) :
    ∃ g : (Fin n → ℝ) → (Fin n → Fin ⌈D / s⌉₊),
      ∀ x ∈ X, ∀ y ∈ X, g x = g y → ‖x - y‖ ≤ s := by
  set K := ⌈D / s⌉₊ with hKdef
  have hK : 1 ≤ K := by
    rw [hKdef, Nat.one_le_ceil_iff]; positivity
  have hcoord : ∀ x y : Fin n → ℝ, ∀ j, |x j - y j| ≤ ‖x - y‖ := by
    intro x y j
    have := norm_le_pi_norm (x - y) j
    rwa [Real.norm_eq_abs, Pi.sub_apply] at this
  let a : Fin n → ℝ := fun j => sInf ((fun x => x j) '' X)
  have hbdd : ∀ j, BddBelow ((fun x : Fin n → ℝ => x j) '' X) := by
    intro j
    refine ⟨x0 j - D, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    have := hcoord x0 y j
    have := hdiam x0 hx0 y hy
    have := le_abs_self (x0 j - y j)
    simp only
    linarith
  have hne : ∀ j, ((fun x : Fin n → ℝ => x j) '' X).Nonempty := fun j => ⟨x0 j, x0, hx0, rfl⟩
  have ha1 : ∀ x ∈ X, ∀ j, a j ≤ x j := fun x hx j => csInf_le (hbdd j) ⟨x, hx, rfl⟩
  have ha2 : ∀ x ∈ X, ∀ j, x j - D ≤ a j := by
    intro x hx j
    apply le_csInf (hne j)
    rintro _ ⟨y, hy, rfl⟩
    have := hcoord x y j
    have := hdiam x hx y hy
    have := le_abs_self (x j - y j)
    simp only
    linarith
  have hKpos : 0 < K := hK
  refine ⟨fun x j => ⟨min ⌊(x j - a j) / s⌋₊ (K - 1), by omega⟩, ?_⟩
  intro x hx y hy hxy
  refine (pi_norm_le_iff_of_nonneg hs.le).mpr (fun j => ?_)
  rw [Real.norm_eq_abs, Pi.sub_apply]
  have hj := congrArg (fun f => (f j : ℕ)) hxy
  simp only at hj
  have hDs : D / s ≤ K := Nat.le_ceil _
  have bnd : ∀ z ∈ X, 0 ≤ (z j - a j) / s ∧ (z j - a j) / s ≤ K := by
    intro z hz
    refine ⟨div_nonneg (sub_nonneg.mpr (ha1 z hz j)) hs.le, ?_⟩
    calc (z j - a j) / s ≤ D / s := by
          apply div_le_div_of_nonneg_right _ hs.le
          linarith [ha2 z hz j]
      _ ≤ K := hDs
  have hc := same_cell K hK _ _ (bnd x hx).1 (bnd x hx).2 (bnd y hy).1 (bnd y hy).2 hj
  have : (x j - a j) / s - (y j - a j) / s = (x j - y j) / s := by ring
  rw [this, abs_div, abs_of_pos hs, div_le_one hs] at hc
  exact hc

lemma hoeff {N : ℕ} {Ξ Ω : Type} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Fin N → Ω → Ξ) (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = Pξ) (hN : 0 < N) (Y : Ξ → ℝ) (hY : Measurable Y)
    (hY01 : ∀ s, Y s ∈ Set.Icc (0 : ℝ) 1) (M : ℝ) (hM : 0 ≤ M) :
    P {ω | (N : ℝ) * M ≤ ∑ i, (Y (ξ i ω) - ∫ s, Y s ∂Pξ)}
      ≤ ENNReal.ofReal (Real.exp (-2 * (N : ℝ) * M ^ 2)) := by
  have hint : ∀ i, (∫ x, Y (ξ i x) ∂P) = ∫ s, Y s ∂Pξ := by
    intro i
    rw [← hlaw i, integral_map (hξ i).aemeasurable hY.aestronglyMeasurable]
  let Z : Fin N → Ω → ℝ := fun i ω => Y (ξ i ω) - (∫ x, Y (ξ i x) ∂P)
  have hindZ : ProbabilityTheory.iIndepFun Z P :=
    hind.comp (fun i s => Y s - (∫ x, Y (ξ i x) ∂P)) (fun i => hY.sub_const _)
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      ProbabilityTheory.HasSubgaussianMGF (Z i) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro i _
    exact ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (hY.comp (hξ i)).aemeasurable
      (ae_of_all _ (fun ω => hY01 _))
  have hNM : 0 ≤ (N : ℝ) * M := by positivity
  have h := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindZ hsub hNM
  have hset : {ω | (N : ℝ) * M ≤ ∑ i, (Y (ξ i ω) - ∫ s, Y s ∂Pξ)}
      = {ω | (N : ℝ) * M ≤ ∑ i ∈ Finset.univ, Z i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Z, hint]
  rw [hset, ← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  refine h.trans (le_of_eq ?_)
  congr 1
  have hc : (((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) : ℝ) = 1 / 4 := by
    simp; norm_num
  rw [NNReal.coe_sum]
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  field_simp
  ring

lemma final_num (N : ℕ) (hN : 0 < N) (SY SG IY F0 Fe α δ β M : ℝ) (hβ : 0 < β) (hM : 0 < M)
    (h1 : SG ≤ SY) (h2 : 1 - (δ - β) ≤ 1 / (N : ℝ) * SG) (h3 : IY ≤ Fe)
    (h4 : M ≤ F0 - Fe + (α - δ)) (h5 : F0 < 1 - α) :
    (N : ℝ) * M ≤ SY - (N : ℝ) * IY := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h2' : (N : ℝ) * (1 - (δ - β)) ≤ SG := by
    have := mul_le_mul_of_nonneg_left h2 hNpos.le
    rwa [← mul_assoc, mul_one_div_cancel hNpos.ne', one_mul] at this
  have h6 : IY ≤ 1 - δ - M := by linarith
  have h7 : (N : ℝ) * IY ≤ (N : ℝ) * (1 - δ - M) := mul_le_mul_of_nonneg_left h6 hNpos.le
  have h8 : 0 ≤ (N : ℝ) * β := by positivity
  nlinarith

end RRAux_SmoothCCP_Feasibility_theorem_3_13

open SmoothCCP.Feasibility in
theorem solution {n N : ℕ} {Ξ Ω : Type} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    (Pξ : Measure Ξ) [IsProbabilityMeasure Pξ] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Fin N → Ω → Ξ) (hξ : ∀ i, Measurable (ξ i)) (hind : ProbabilityTheory.iIndepFun ξ P)
    (hlaw : ∀ i, P.map (ξ i) = Pξ) (hN : 1 ≤ N)
    (C : (Fin n → ℝ) → Ξ → ℝ) (X : Set (Fin n → ℝ)) (hX : IsClosed X)
    (hC : ∀ x ∈ X, Measurable (C x)) (hcont : ∀ x ∈ X, ∀ y : ℝ, Pξ {s | C x s = y} = 0)
    (α ε : ℝ) (γ : ℝ → ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hγ : AdmissibleGamma ε γ)
    (D : ℝ) (hD : 0 < D) (hdiam : ∀ x ∈ X, ∀ y ∈ X, ‖x - y‖ ≤ D)
    (L : ℝ) (hL : 0 < L) (hLip : ∀ᵐ s ∂Pξ, ∀ x ∈ X, ∀ y ∈ X, |C x s - C y s| ≤ L * ‖x - y‖)
    (t δ M : ℝ) (ht : 0 < t) (hδ0 : 0 < δ) (hδα : δ ≤ α) (hM : 0 < M)
    (hMx : ∀ x ∈ X, M ≤ margin Pξ C ε γ t α δ x)
    (β : ℝ) (hβ0 : 0 < β) (hβδ : β ≤ δ) :
    P {ω | ¬ sampleFeasible C X ε γ (fun i => ξ i ω) (2 * t) (δ - β) ⊆ trueFeasible Pξ C X α}
      ≤ ENNReal.ofReal
          ((⌈1 / β⌉₊ : ℝ) * (⌈2 * L * D / t⌉₊ : ℝ) ^ n * Real.exp (-2 * (N : ℝ) * M ^ 2)) := by
  rcases X.eq_empty_or_nonempty with hXe | ⟨x0, hx0⟩
  · have : {ω | ¬ sampleFeasible C X ε γ (fun i => ξ i ω) (2 * t) (δ - β)
        ⊆ trueFeasible Pξ C X α} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      intro x hx
      exact absurd hx.1 (by rw [hXe]; exact Set.notMem_empty x)
    rw [this, measure_empty]
    exact zero_le
  have hNpos : 0 < N := hN
  set s := t / (2 * L) with hsdef
  have hs : 0 < s := by positivity
  have hLs : L * s = t / 2 := by rw [hsdef]; field_simp
  obtain ⟨g, hg⟩ := RRAux_SmoothCCP_Feasibility_theorem_3_13.grid X x0 hx0 D hD hdiam s hs
  have hKeq : D / s = 2 * L * D / t := by rw [hsdef]; field_simp
  classical
  let r : (Fin n → Fin ⌈D / s⌉₊) → (Fin n → ℝ) := fun κ =>
    if h : ∃ x ∈ X, g x = κ then h.choose else x0
  have hrX : ∀ κ, r κ ∈ X := by
    intro κ
    by_cases h : ∃ x ∈ X, g x = κ
    · simp only [r, dif_pos h]; exact h.choose_spec.1
    · simp only [r, dif_neg h]; exact hx0
  have hr : ∀ x ∈ X, ‖x - r (g x)‖ ≤ s := by
    intro x hx
    have h : ∃ y ∈ X, g y = g x := ⟨x, hx, rfl⟩
    have e : r (g x) = h.choose := by simp only [r, dif_pos h]
    rw [e]
    exact hg x hx _ h.choose_spec.1 h.choose_spec.2.symm
  let Y : (Fin n → Fin ⌈D / s⌉₊) → Ξ → ℝ := fun κ u => Gam ε γ (C (r κ) u + 3 * t / 2)
  have hYm : ∀ κ, Measurable (Y κ) := fun κ =>
    (RRAux_SmoothCCP_Feasibility_theorem_3_13.gam_meas hγ).comp ((hC _ (hrX κ)).add_const _)
  have hY01 : ∀ κ u, Y κ u ∈ Set.Icc (0 : ℝ) 1 := fun κ u =>
    RRAux_SmoothCCP_Feasibility_theorem_3_13.gam_mem hγ _
  let E : (Fin n → Fin ⌈D / s⌉₊) → Set Ω := fun κ =>
    {ω | (N : ℝ) * M ≤ ∑ i, (Y κ (ξ i ω) - ∫ u, Y κ u ∂Pξ)}
  let G : Set Ξ := {u | ∀ x ∈ X, ∀ y ∈ X, |C x u - C y u| ≤ L * ‖x - y‖}
  have hnull : P {ω | ¬ ∀ i, ξ i ω ∈ G} = 0 := by
    have : ∀ᵐ ω ∂P, ∀ i, ξ i ω ∈ G :=
      ae_all_iff.mpr (fun i => ae_of_ae_map (hξ i).aemeasurable (by rw [hlaw i]; exact hLip))
    exact ae_iff.mp this
  have hsub : {ω | ¬ sampleFeasible C X ε γ (fun i => ξ i ω) (2 * t) (δ - β)
      ⊆ trueFeasible Pξ C X α} ⊆ {ω | ¬ ∀ i, ξ i ω ∈ G} ∪ ⋃ κ, E κ := by
    intro ω hω
    by_cases hGω : ∀ i, ξ i ω ∈ G
    · right
      obtain ⟨x, hxS, hxT⟩ := Set.not_subset.mp hω
      have hxX : x ∈ X := hxS.1
      have hF0 : cdf Pξ C 0 x < 1 - α := by
        by_contra hc
        exact hxT ⟨hxX, not_lt.mp hc⟩
      refine Set.mem_iUnion.mpr ⟨g x, ?_⟩
      set x' := r (g x) with hx'
      have hx'X : x' ∈ X := hrX _
      have hd : ‖x' - x‖ ≤ s := by rw [norm_sub_rev]; exact hr x hxX
      have hLip' : ∀ u ∈ G, |C x' u - C x u| ≤ t / 2 := by
        intro u hu
        have := hu x' hx'X x hxX
        have h2 : L * ‖x' - x‖ ≤ L * s := mul_le_mul_of_nonneg_left hd hL.le
        linarith
      -- sample side
      have hpt : ∀ i, Gam ε γ (C x (ξ i ω) - -(2 * t)) ≤ Y (g x) (ξ i ω) := by
        intro i
        apply RRAux_SmoothCCP_Feasibility_theorem_3_13.gam_anti hγ
        have := (abs_le.mp (hLip' _ (hGω i))).2
        show C x' (ξ i ω) + 3 * t / 2 ≤ C x (ξ i ω) - -(2 * t)
        linarith
      have hsum : ∑ i, Gam ε γ (C x (ξ i ω) - -(2 * t)) ≤ ∑ i, Y (g x) (ξ i ω) :=
        Finset.sum_le_sum (fun i _ => hpt i)
      -- expectation side
      have hint1 : Integrable (Y (g x)) Pξ :=
        Integrable.of_mem_Icc 0 1 (hYm _).aemeasurable (ae_of_all _ (hY01 _))
      have hm2 : Measurable (fun u => Gam ε γ (C x u - -t)) :=
        (RRAux_SmoothCCP_Feasibility_theorem_3_13.gam_meas hγ).comp ((hC x hxX).sub_const _)
      have hint2 : Integrable (fun u => Gam ε γ (C x u - -t)) Pξ :=
        Integrable.of_mem_Icc 0 1 hm2.aemeasurable
          (ae_of_all _ (fun u => RRAux_SmoothCCP_Feasibility_theorem_3_13.gam_mem hγ _))
      have hIY : ∫ u, Y (g x) u ∂Pξ ≤ smoothCdf Pξ C ε γ (-t) x := by
        unfold smoothCdf
        apply integral_mono_ae hint1 hint2
        filter_upwards [hLip] with u hu
        apply RRAux_SmoothCCP_Feasibility_theorem_3_13.gam_anti hγ
        have := (abs_le.mp (hLip' u hu)).1
        show C x u - -t ≤ C x' u + 3 * t / 2
        linarith
      have hmar := hMx x hxX
      unfold margin at hmar
      have hS := hxS.2
      unfold sampleCdf at hS
      show (N : ℝ) * M ≤ ∑ i, (Y (g x) (ξ i ω) - ∫ u, Y (g x) u ∂Pξ)
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      exact RRAux_SmoothCCP_Feasibility_theorem_3_13.final_num N hNpos _ _ _ _ _ α δ β M
        hβ0 hM hsum hS hIY hmar hF0
    · left; exact hGω
  have hE : ∀ κ, P (E κ) ≤ ENNReal.ofReal (Real.exp (-2 * (N : ℝ) * M ^ 2)) := fun κ =>
    RRAux_SmoothCCP_Feasibility_theorem_3_13.hoeff Pξ P ξ hξ hind hlaw hNpos (Y κ) (hYm κ)
      (hY01 κ) M hM.le
  calc P {ω | ¬ sampleFeasible C X ε γ (fun i => ξ i ω) (2 * t) (δ - β) ⊆ trueFeasible Pξ C X α}
      ≤ P ({ω | ¬ ∀ i, ξ i ω ∈ G} ∪ ⋃ κ, E κ) := measure_mono hsub
    _ ≤ P {ω | ¬ ∀ i, ξ i ω ∈ G} + P (⋃ κ, E κ) := measure_union_le _ _
    _ ≤ 0 + ∑ κ, P (E κ) := by rw [hnull]; gcongr; exact measure_iUnion_fintype_le _ _
    _ ≤ ∑ _κ : Fin n → Fin ⌈D / s⌉₊, ENNReal.ofReal (Real.exp (-2 * (N : ℝ) * M ^ 2)) := by
        rw [zero_add]; exact Finset.sum_le_sum (fun κ _ => hE κ)
    _ = ENNReal.ofReal (∑ _κ : Fin n → Fin ⌈D / s⌉₊, Real.exp (-2 * (N : ℝ) * M ^ 2)) :=
        (ENNReal.ofReal_sum_of_nonneg (fun _ _ => (Real.exp_pos _).le)).symm
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, hKeq]
        have h1 : (1 : ℝ) ≤ (⌈1 / β⌉₊ : ℝ) := by
          have : 1 ≤ ⌈1 / β⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
          exact_mod_cast this
        have h2 : 0 ≤ (⌈2 * L * D / t⌉₊ : ℝ) ^ n * Real.exp (-2 * (N : ℝ) * M ^ 2) := by
          positivity
        exact (le_mul_of_one_le_left h2 h1).trans_eq (by ring)

#print axioms solution
