-- Prove2me | solution 1 for ZudilinZeta.zudilin_phi_tail_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T10:40:59.4346+00:00
-- url     : https://prove2.me/submissions/938d782c-b665-4e05-aa4d-6189920cf53b

import Definitions.Def_ZudilinZetaAsymp
import Theorems.Thm_Zeta23_Stirling_hasSum_trigamma
import Theorems.Thm_Zeta23_Stirling_differentiableAt_digamma
import Theorems.Thm_ZudilinZeta_zudilin_phi_nonneg_periodic

open Filter MeasureTheory Set ZudilinZeta
open scoped Topology

private lemma digamma_eq_re {x : ℝ} (hx : 0 < x) :
    ZudilinZeta.digamma x = (Complex.digamma x).re := by
  have hR : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma (fun n hn => by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
  have hC : DifferentiableAt ℂ Complex.Gamma (x : ℂ) :=
    Complex.differentiableAt_Gamma _ (fun n hn => by
      have := congrArg Complex.re hn
      simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at this
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)
  have hd : deriv Real.Gamma x = (deriv Complex.Gamma (x : ℂ)).re := by
    simpa only [Complex.Gamma_ofReal, Complex.ofReal_re] using hC.hasDerivAt.real_of_complex.deriv
  rw [ZudilinZeta.digamma, hR.hasDerivAt.log (Real.Gamma_pos_of_pos hx).ne' |>.deriv,
    Complex.digamma, logDeriv_apply, Complex.Gamma_ofReal, Complex.div_ofReal_re, hd]

private lemma hasSum_real_trigamma {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasSum (fun n : ℕ => 1 / (x + (n : ℝ)) ^ 2) (deriv ZudilinZeta.digamma x) := by
  have hxc : (x : ℂ) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨n, hn⟩
    have hnR : (n : ℝ) = x := by
      simpa only [Complex.intCast_re, Complex.ofReal_re] using congrArg Complex.re hn
    have hnp : (0 : ℤ) < n := by exact_mod_cast (hnR ▸ hx)
    have hnl : n < (1 : ℤ) := by exact_mod_cast (hnR ▸ hx1)
    omega
  have hd := (Zeta23.Stirling.differentiableAt_digamma hxc).hasDerivAt.real_of_complex
  have heq : (fun t : ℝ => (Complex.digamma t).re) =ᶠ[𝓝 x] ZudilinZeta.digamma := by
    filter_upwards [eventually_gt_nhds hx] with t ht using (digamma_eq_re ht).symm
  have hd' := (hd.congr_of_eventuallyEq heq.symm).deriv
  rw [hd']
  convert Complex.hasSum_re (Zeta23.Stirling.hasSum_trigamma hxc) using 1
  ext n
  norm_cast

private lemma hasSum_positive_unit_integrals {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioi 0)) :
    HasSum (fun n : ℕ => ∫ x in (n : ℝ)..(n : ℝ) + 1, g x)
      (∫ x in Ioi (0 : ℝ), g x) := by
  have hu : (⋃ n : ℕ, Ico (n : ℝ) ((n : ℝ) + 1)) = Ici (0 : ℝ) := by
    ext x
    simp only [mem_iUnion, mem_Ico, mem_Ici]
    constructor
    · rintro ⟨n, hn, _⟩
      exact (Nat.cast_nonneg n).trans hn
    · intro hx
      exact ⟨⌊x⌋₊, Nat.floor_le hx, Nat.lt_floor_add_one x⟩
  have hd : Pairwise (fun n m : ℕ =>
      Disjoint (Ico (n : ℝ) ((n : ℝ) + 1)) (Ico (m : ℝ) ((m : ℝ) + 1))) := by
    intro n m hnm
    rcases lt_or_gt_of_ne hnm with h | h
    · apply Set.disjoint_left.mpr
      intro x hx hy
      have hh : (n : ℝ) + 1 ≤ m := by exact_mod_cast h
      linarith [hx.2, hy.1]
    · apply Set.disjoint_left.mpr
      intro x hx hy
      have hh : (m : ℝ) + 1 ≤ n := by exact_mod_cast h
      linarith [hy.2, hx.1]
  have hgi : IntegrableOn g (⋃ n : ℕ, Ico (n : ℝ) ((n : ℝ) + 1)) := by
    rw [hu, integrableOn_Ici_iff_integrableOn_Ioi]
    exact hg
  have hs := hasSum_integral_iUnion (fun n : ℕ => measurableSet_Ico) hd hgi
  rw [hu, integral_Ici_eq_integral_Ioi] at hs
  apply HasSum.congr_fun hs
  intro n
  rw [intervalIntegral.integral_of_le (by linarith), integral_Ico_eq_integral_Ioc]

private lemma periodic_weighted_integral {f : ℝ → ℝ}
    (hp : Function.Periodic f 1) (hf : IntegrableOn (fun x => f x / x ^ 2) (Ioi 0)) :
    (∫ x in Ioi (0 : ℝ), f x / x ^ 2) =
      ∫ x in (0 : ℝ)..1, f x * deriv ZudilinZeta.digamma x := by
  let g : ℝ → ℝ := fun x => f x / x ^ 2
  have hper (n : ℕ) (x : ℝ) : f (x + (n : ℝ)) = f x := by
    simpa only [mul_one] using hp.nat_mul n x
  have hloc (n : ℕ) : IntervalIntegrable g volume (n : ℝ) ((n : ℝ) + 1) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
    exact hf.mono_set (fun x hx => lt_of_le_of_lt (Nat.cast_nonneg n) hx.1)
  have hshift (n : ℕ) : IntervalIntegrable (fun x => g (x + (n : ℝ))) volume 0 1 := by
    simpa only [sub_self, add_sub_cancel_left] using (hloc n).comp_add_right (n : ℝ)
  have hsum : Summable (fun n : ℕ => ∫ x in (0 : ℝ)..1, ‖g (x + (n : ℝ))‖) := by
    have hs := (hasSum_positive_unit_integrals hf.norm).summable
    convert hs using 1
    ext n
    simpa only [g, zero_add, add_comm (1 : ℝ)] using
      intervalIntegral.integral_comp_add_right (fun x => ‖g x‖) (a := 0) (b := 1) (n : ℝ)
  have hi := hasSum_integral_of_summable_integral_norm
    (fun n : ℕ => (hshift n).1) (by
      simpa only [intervalIntegral.integral_of_le zero_le_one] using hsum)
  have hval : (∫ x in Ioc (0 : ℝ) 1, ∑' n : ℕ, g (x + (n : ℝ))) =
      ∫ x in (0 : ℝ)..1, f x * deriv ZudilinZeta.digamma x := by
    rw [intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    have hs := (hasSum_real_trigamma hx.1 hx.2).mul_left (f x)
    dsimp only
    rw [← hs.tsum_eq]
    apply tsum_congr
    intro n
    simp only [g, hper, mul_one_div]
  rw [hval] at hi
  have hs := hasSum_positive_unit_integrals hf
  apply hs.unique
  apply HasSum.congr_fun hi
  intro n
  symm
  change (∫ x in Ioc (0 : ℝ) 1, g (x + (n : ℝ))) =
    ∫ x in (n : ℝ)..(n : ℝ) + 1, g x
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_add_right]
  simp only [zero_add, add_comm (1 : ℝ)]

private lemma sigma_inter {X : Type*} [TopologicalSpace X] [T2Space X]
    {s t : Set X} (hs : IsSigmaCompact s) (ht : IsSigmaCompact t) : IsSigmaCompact (s ∩ t) := by
  obtain ⟨K, hK, rfl⟩ := hs
  obtain ⟨L, hL, rfl⟩ := ht
  simp only [iUnion_inter, inter_iUnion]
  apply isSigmaCompact_iUnion
  intro n
  apply isSigmaCompact_iUnion
  intro m
  exact ((hK m).inter (hL n)).isSigmaCompact

private lemma sigma_locallyClosed {s : Set (ℝ × ℝ)} (hs : IsLocallyClosed s) :
    IsSigmaCompact s := by
  let : LocallyCompactSpace s := hs.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance

private lemma sigma_measurable {s : Set ℝ} (hs : IsSigmaCompact s) : MeasurableSet s := by
  obtain ⟨K, hK, rfl⟩ := hs
  exact MeasurableSet.iUnion fun n => (hK n).measurableSet

private def CompactFibers (f : ℝ × ℝ → ℤ) : Prop :=
  ∀ k : ℤ, IsSigmaCompact {z | f z = k}

private lemma compactFibers_const (c : ℤ) : CompactFibers (fun _ => c) := by
  intro k
  by_cases h : c = k
  · simpa [h] using (isSigmaCompact_univ : IsSigmaCompact (univ : Set (ℝ × ℝ)))
  · simp [h]

private lemma compactFibers_op {f g : ℝ × ℝ → ℤ}
    (hf : CompactFibers f) (hg : CompactFibers g) (op : ℤ → ℤ → ℤ) :
    CompactFibers (fun z => op (f z) (g z)) := by
  intro k
  have heq : {z | op (f z) (g z) = k} =
      ⋃ p : {p : ℤ × ℤ // op p.1 p.2 = k}, {z | f z = p.1.1} ∩ {z | g z = p.1.2} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    constructor
    · intro h
      exact ⟨⟨(f z, g z), h⟩, rfl, rfl⟩
    · rintro ⟨p, hf, hg⟩
      simpa only [hf, hg] using p.2
  rw [heq]
  exact isSigmaCompact_iUnion _ fun p => sigma_inter (hf p.1.1) (hg p.1.2)

private lemma compactFibers_floor {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    CompactFibers (fun z => ⌊f z⌋) := by
  intro k
  have heq : {z | ⌊f z⌋ = k} = {z | (k : ℝ) ≤ f z} ∩ {z | f z < (k : ℝ) + 1} := by
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, Int.floor_eq_iff]
  rw [heq]
  apply sigma_locallyClosed
  exact ((isClosed_le continuous_const hf).isLocallyClosed).inter
    ((isOpen_lt hf continuous_const).isLocallyClosed)

private lemma compactFibers_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ × ℝ → ℤ)
    (hf : ∀ i ∈ s, CompactFibers (f i)) : CompactFibers (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using compactFibers_const 0
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact compactFibers_op (hf i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))) (· + ·)

private lemma phiExpr_compactFibers (P : Params) : CompactFibers (fun z => phiExpr P z.1 z.2) := by
  unfold phiExpr
  apply compactFibers_op _ _ (· + ·)
  · apply compactFibers_sum
    intro j hj
    repeat' first | apply compactFibers_op _ _ (· - ·)
                  | apply compactFibers_op _ _ (· + ·)
                  | apply compactFibers_op _ _ (· * ·)
                  | apply compactFibers_const
                  | apply compactFibers_floor
    all_goals fun_prop
  · apply compactFibers_sum
    intro j hj
    repeat' first | apply compactFibers_op _ _ (· - ·)
                  | apply compactFibers_floor
    all_goals fun_prop

-- The following floor-superadditivity proof reuses the argument in the accepted
-- Prove2Me submission c74c01b0-dbc0-4054-acf6-232df78455ed (cm_beta).
private lemma phiExpr_nonneg (P : Params) (x y : ℝ) : 0 ≤ phiExpr P x y := by
  have h1 (e0 ej : ℝ) :
      0 ≤ ⌊y⌋ + ⌊e0 * x - y⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ - 2 * ⌊ej * x⌋ := by
    have ha : ⌊(e0 - ej) * x - y⌋ + ⌊ej * x⌋ ≤ ⌊e0 * x - y⌋ := by
      rw [Int.le_floor]; push_cast
      linarith [Int.floor_le ((e0 - ej) * x - y), Int.floor_le (ej * x)]
    have hb : ⌊ej * x⌋ + ⌊y - ej * x⌋ ≤ ⌊y⌋ := by
      rw [Int.le_floor]; push_cast
      linarith [Int.floor_le (y - ej * x), Int.floor_le (ej * x)]
    omega
  have h2 (e0 ej : ℝ) :
      0 ≤ ⌊(e0 - 2 * ej) * x⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ := by
    have h : ⌊y - ej * x⌋ + ⌊(e0 - ej) * x - y⌋ ≤ ⌊(e0 - 2 * ej) * x⌋ := by
      rw [Int.le_floor]; push_cast
      linarith [Int.floor_le (y - ej * x), Int.floor_le ((e0 - ej) * x - y)]
    omega
  exact add_nonneg (Finset.sum_nonneg (fun _ _ => h1 _ _))
    (Finset.sum_nonneg (fun _ _ => h2 _ _))

private lemma phiExpr_bddBelow (P : Params) (x : ℝ) :
    BddBelow (phiExpr P x '' Ico (0 : ℝ) 1) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨y, _, rfl⟩
  exact phiExpr_nonneg P x y

private lemma phi_measurable (P : Params) : Measurable (phi P) := by
  apply measurable_of_Iic
  intro k
  let s : Set (ℝ × ℝ) := {z | z.2 ∈ Ico (0 : ℝ) 1 ∧ phiExpr P z.1 z.2 ≤ k}
  have hf : IsSigmaCompact {z : ℝ × ℝ | phiExpr P z.1 z.2 ≤ k} := by
    have heq : {z : ℝ × ℝ | phiExpr P z.1 z.2 ≤ k} =
        ⋃ a : {a : ℤ // a ≤ k}, {z | phiExpr P z.1 z.2 = a.1} := by
      ext z
      simp only [mem_ofPred_eq, mem_iUnion]
      exact ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨a, h⟩ => h ▸ a.2⟩
    rw [heq]
    exact isSigmaCompact_iUnion _ (fun a => phiExpr_compactFibers P a.1)
  have hs : IsSigmaCompact s := by
    apply sigma_inter _ hf
    apply sigma_locallyClosed
    exact ((isClosed_le continuous_const continuous_snd).isLocallyClosed).inter
      ((isOpen_lt continuous_snd continuous_const).isLocallyClosed)
  have heq : phi P ⁻¹' Iic k = Prod.fst '' s := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, he⟩ := Int.csInf_mem
        (show (phiExpr P x '' Ico (0 : ℝ) 1).Nonempty from ⟨_, 0, ⟨le_rfl, one_pos⟩, rfl⟩)
        (phiExpr_bddBelow P x)
      exact ⟨(x, y), ⟨hy, he.trans_le hx⟩, rfl⟩
    · rintro ⟨⟨a, y⟩, hy, rfl⟩
      exact (csInf_le (phiExpr_bddBelow P a) ⟨y, hy.1, rfl⟩).trans hy.2
  rw [heq]
  exact sigma_measurable (hs.image continuous_fst)

private lemma phi_bounded (P : Params) (x : ℝ) :
    phi P x ≤ 2 * ((Finset.Icc 1 P.r).card : ℤ) + (Finset.Icc (P.r + 1) P.q).card := by
  have h1 (e0 ej y : ℝ) :
      ⌊y⌋ + ⌊e0 * x - y⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ - 2 * ⌊ej * x⌋ ≤ 2 := by
    have ha := Int.le_floor_add_floor ((e0 - ej) * x - y) (ej * x)
    have hb := Int.le_floor_add_floor (ej * x) (y - ej * x)
    rw [show (e0 - ej) * x - y + ej * x = e0 * x - y by ring] at ha
    rw [show ej * x + (y - ej * x) = y by ring] at hb
    omega
  have h2 (e0 ej y : ℝ) :
      ⌊(e0 - 2 * ej) * x⌋ - ⌊y - ej * x⌋ - ⌊(e0 - ej) * x - y⌋ ≤ 1 := by
    have h := Int.le_floor_add_floor (y - ej * x) ((e0 - ej) * x - y)
    rw [show y - ej * x + ((e0 - ej) * x - y) = (e0 - 2 * ej) * x by ring] at h
    omega
  apply (csInf_le (phiExpr_bddBelow P x) (show phiExpr P x 0 ∈ _ from
    ⟨0, ⟨le_rfl, one_pos⟩, rfl⟩)).trans
  have hsum := add_le_add (Finset.sum_le_sum (s := Finset.Icc 1 P.r) (fun j _ => h1 (P.eta 0) (P.eta j) 0))
    (Finset.sum_le_sum (s := Finset.Icc (P.r + 1) P.q) (fun j _ => h2 (P.eta 0) (P.eta j) 0))
  simpa [phiExpr, mul_comm] using hsum

private lemma eta_le_last (P : Params) (j : ℕ) (hj : j ∈ Finset.Icc 1 P.q) : P.eta j ≤ P.eta P.q := by
  have hm (k : ℕ) : ∀ i, 1 ≤ i → i + k ≤ P.q → P.eta i ≤ P.eta (i + k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro i hi hik
      have h1 := ih i hi (by omega)
      have h2 := P.eta_mono (i + k) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
      simpa only [Nat.add_assoc] using h1.trans h2
  have h := hm (P.q - j) j (Finset.mem_Icc.mp hj).1 (by have := (Finset.mem_Icc.mp hj).2; omega)
  simpa only [Nat.add_sub_of_le (Finset.mem_Icc.mp hj).2] using h

private lemma phi_zero_near_zero (P : Params) {x : ℝ} (hx : 0 ≤ x)
    (hx1 : (P.eta 0 : ℝ) * x < 1) : phi P x = 0 := by
  have hq : 0 ≤ (P.eta P.q : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
  have hq2 : 2 * ((P.eta P.q : ℝ) * x) ≤ (P.eta 0 : ℝ) * x := by
    have he : 2 * (P.eta P.q : ℝ) ≤ P.eta 0 := by exact_mod_cast P.eta_lt.le
    nlinarith [mul_le_mul_of_nonneg_right he hx]
  have hy : (P.eta P.q : ℝ) * x ∈ Ico (0 : ℝ) 1 := ⟨hq, by linarith⟩
  have hfy : ⌊(P.eta P.q : ℝ) * x⌋ = 0 := Int.floor_eq_zero_iff.mpr hy
  have hf0 : ⌊(P.eta 0 : ℝ) * x - (P.eta P.q : ℝ) * x⌋ = 0 :=
    Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
  have hterms (j : ℕ) (hj : j ∈ Finset.Icc 1 P.q) :
      (⌊(P.eta P.q : ℝ) * x - (P.eta j : ℝ) * x⌋ = 0) ∧
      (⌊((P.eta 0 : ℝ) - (P.eta j : ℝ)) * x - (P.eta P.q : ℝ) * x⌋ = 0) ∧
      (⌊(P.eta j : ℝ) * x⌋ = 0) ∧
      (⌊((P.eta 0 : ℝ) - 2 * (P.eta j : ℝ)) * x⌋ = 0) := by
    have hja : 0 ≤ (P.eta j : ℝ) * x := mul_nonneg (Nat.cast_nonneg _) hx
    have hjb : (P.eta j : ℝ) * x ≤ (P.eta P.q : ℝ) * x :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast eta_le_last P j hj) hx
    refine ⟨Int.floor_eq_zero_iff.mpr ?_, Int.floor_eq_zero_iff.mpr ?_,
      Int.floor_eq_zero_iff.mpr ?_, Int.floor_eq_zero_iff.mpr ?_⟩ <;>
      constructor <;> nlinarith
  have he : phiExpr P x ((P.eta P.q : ℝ) * x) = 0 := by
    unfold phiExpr
    refine (congrArg₂ (· + ·) ?_ ?_).trans (zero_add (0 : ℤ))
    · apply Finset.sum_eq_zero
      intro j hj
      have hj' : j ∈ Finset.Icc 1 P.q := by
        have := Finset.mem_Icc.mp hj
        have := P.q_ge
        apply Finset.mem_Icc.mpr
        omega
      obtain ⟨ha, hb, hc, _⟩ := hterms j hj'
      simp only [hfy, hf0, ha, hb, hc]
      norm_num
    · apply Finset.sum_eq_zero
      intro j hj
      have hj' : j ∈ Finset.Icc 1 P.q := by
        have := Finset.mem_Icc.mp hj
        apply Finset.mem_Icc.mpr
        omega
      obtain ⟨ha, hb, _, hc⟩ := hterms j hj'
      simp only [ha, hb, hc]
      norm_num
  exact le_antisymm ((csInf_le (phiExpr_bddBelow P x) ⟨_, hy, rfl⟩).trans_eq he)
    ((zudilin_phi_nonneg_periodic P).1 x)

private lemma phi_weighted_integrable (P : Params) :
    IntegrableOn (fun x : ℝ => (phi P x : ℝ) / x ^ 2) (Ioi 0) := by
  let δ : ℝ := 1 / ((P.eta 0 : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : (P.eta 0 : ℝ) * δ < 1 := by
    dsimp [δ]
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith
  let B : ℝ := 2 * ((Finset.Icc 1 P.r).card : ℝ) + (Finset.Icc (P.r + 1) P.q).card
  have hb (x : ℝ) : (phi P x : ℝ) ≤ B := by
    dsimp [B]
    exact_mod_cast phi_bounded P x
  have hnonneg (x : ℝ) : 0 ≤ (phi P x : ℝ) := by
    exact_mod_cast (zudilin_phi_nonneg_periodic P).1 x
  have hmeas : Measurable (fun x : ℝ => (phi P x : ℝ) / x ^ 2) := by
    exact ((measurable_of_countable (fun n : ℤ => (n : ℝ))).comp (phi_measurable P)).div
      (measurable_id.pow_const 2)
  have htail : IntegrableOn (fun x : ℝ => (phi P x : ℝ) / x ^ 2) (Ioi δ) := by
    have hbase : IntegrableOn (fun x : ℝ => 1 / x ^ 2) (Ioi δ) := by
      simpa only [Real.rpow_neg_ofNat, zpow_neg, zpow_ofNat, one_div] using
        (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hδ)
    have hdom := hbase.const_mul B
    apply hdom.mono' hmeas.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hnonneg x) (sq_nonneg x)), mul_one_div]
    exact div_le_div_of_nonneg_right (hb x) (sq_nonneg x)
  have hhead : IntegrableOn (fun x : ℝ => (phi P x : ℝ) / x ^ 2) (Ioc 0 δ) := by
    refine (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioc 0 δ)).congr_fun ?_ measurableSet_Ioc
    intro x hx
    have hz := phi_zero_near_zero P hx.1.le
      ((mul_le_mul_of_nonneg_left hx.2 (Nat.cast_nonneg _)).trans_lt hδ1)
    simp only [hz, Int.cast_zero, zero_div]
  simpa only [Ioc_union_Ioi_eq_Ioi hδ.le] using hhead.union htail

theorem solution (P : Params) :
    (∫ x in Set.Ioi (1 / (m P (P.q - P.r) : ℝ)), (phi P x : ℝ) / x ^ 2) =
      (∫ x in (0 : ℝ)..1, (phi P x : ℝ) * deriv digamma x) -
        ∫ x in (0 : ℝ)..(1 / (m P (P.q - P.r) : ℝ)),
          (phi P x : ℝ) / x ^ 2 := by
  have hp : Function.Periodic (fun x => (phi P x : ℝ)) 1 := by
    intro x
    dsimp only
    rw [(zudilin_phi_nonneg_periodic P).2 x]
  have hf := phi_weighted_integrable P
  have hi := periodic_weighted_integral hp hf
  have ha : 0 ≤ 1 / (m P (P.q - P.r) : ℝ) := by positivity
  have hs := intervalIntegral.integral_Ioi_sub_Ioi hf ha
  rw [hi] at hs
  linarith
