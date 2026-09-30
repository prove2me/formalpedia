-- Prove2me | solution 1 for RevenueManagement.first_price_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T23:42:14.095976+00:00
-- url     : https://prove2.me/submissions/6c61566b-6757-4983-920e-668c723cda79

import Definitions.Def_RevenueManagement_auctions

namespace RevenueManagement

open Set

variable (V : PrivateValues)

lemma fp_Fcont (hV : V.IsRegular) : ContinuousOn V.F (Icc 0 V.vbar) :=
  fun v hv => (hV.2.2.2.2.2 v hv).continuousWithinAt

lemma fp_Fstrict (hV : V.IsRegular) : StrictMonoOn V.F (Icc 0 V.vbar) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 V.vbar) (fp_Fcont V hV)
  intro x hx
  rw [interior_Icc] at hx
  have h := (hV.2.2.2.2.2 x (Ioo_subset_Icc_self hx)).hasDerivAt (Icc_mem_nhds hx.1 hx.2)
  rw [h.deriv]
  exact hV.2.2.2.2.1 x (Ioo_subset_Icc_self hx)

lemma fp_Fpos (hV : V.IsRegular) {v : ℝ} (hv : v ∈ Ioc 0 V.vbar) : 0 < V.F v := by
  have := fp_Fstrict V hV ⟨le_rfl, hV.1.le⟩ (Ioc_subset_Icc_self hv) hv.1
  rwa [hV.2.1] at this

lemma fp_Fnn (hV : V.IsRegular) {v : ℝ} (hv : v ∈ Icc 0 V.vbar) : 0 ≤ V.F v := by
  rcases hv.1.lt_or_eq with h | h
  · exact (fp_Fpos V hV ⟨h, hv.2⟩).le
  · rw [← h, hV.2.1]

lemma fp_Pcont (hV : V.IsRegular) : ContinuousOn (firstPriceWinProb V) (Icc 0 V.vbar) := by
  unfold firstPriceWinProb
  exact (fp_Fcont V hV).pow _

lemma fp_Pmono (hV : V.IsRegular) : MonotoneOn (firstPriceWinProb V) (Icc 0 V.vbar) := by
  intro a ha b hb hab
  exact pow_le_pow_left₀ (fp_Fnn V hV ha) ((fp_Fstrict V hV).monotoneOn ha hb hab) _

lemma fp_Ppos (hV : V.IsRegular) {v : ℝ} (hv : v ∈ Ioc 0 V.vbar) :
    0 < firstPriceWinProb V v :=
  pow_pos (fp_Fpos V hV hv) _

lemma fp_int (hV : V.IsRegular) {a b : ℝ} (ha : a ∈ Icc 0 V.vbar) (hb : b ∈ Icc 0 V.vbar) :
    IntervalIntegrable (firstPriceWinProb V) MeasureTheory.volume a b :=
  ((fp_Pcont V hV).mono (uIcc_subset_Icc ha hb)).intervalIntegrable

/-- The fundamental theorem of calculus for `∫₀ᵘ P` within `[0, vbar]`, via the continuous
extension of `P` by clamping. -/
lemma fp_Ideriv (hV : V.IsRegular) {v : ℝ} (hv : v ∈ Icc 0 V.vbar) :
    HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, firstPriceWinProb V s)
      (firstPriceWinProb V v) (Icc 0 V.vbar) v := by
  let g : ℝ → ℝ := fun u => firstPriceWinProb V (projIcc 0 V.vbar hV.1.le u)
  have hgc : Continuous g :=
    (fp_Pcont V hV).comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      (fun u => (projIcc 0 V.vbar hV.1.le u).2)
  have hgeq : ∀ u ∈ Icc 0 V.vbar, g u = firstPriceWinProb V u := fun u hu => by
    simp only [g, projIcc_of_mem hV.1.le hu]
  have hd := (hgc.integral_hasStrictDerivAt 0 v).hasDerivAt.hasDerivWithinAt (s := Icc 0 V.vbar)
  rw [hgeq v hv] at hd
  refine hd.congr (fun u hu => ?_) ?_
  · refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hu.1] at hs
    exact (hgeq s ⟨hs.1, hs.2.trans hu.2⟩).symm
  · refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hv.1] at hs
    exact (hgeq s ⟨hs.1, hs.2.trans hv.2⟩).symm

lemma fp_a (hV : V.IsRegular) (hN : 2 ≤ V.N) (v : ℝ) (hv : v ∈ Ioc 0 V.vbar) :
    HasDerivWithinAt (firstPriceBid V)
      ((((V.N : ℝ) - 1) * V.F v ^ (V.N - 2) * V.f v / firstPriceWinProb V v) *
        (v - firstPriceBid V v)) (Icc 0 V.vbar) v := by
  have hvI : v ∈ Icc 0 V.vbar := Ioc_subset_Icc_self hv
  have hPv := fp_Ppos V hV hv
  have hP : HasDerivWithinAt (firstPriceWinProb V)
      (((V.N - 1 : ℕ) : ℝ) * V.F v ^ (V.N - 1 - 1) * V.f v) (Icc 0 V.vbar) v :=
    (hV.2.2.2.2.2 v hvI).pow (V.N - 1)
  have hI := fp_Ideriv V hV hvI
  have h := (hasDerivWithinAt_id v (Icc 0 V.vbar)).sub (hI.div hP hPv.ne')
  have hcast : ((V.N - 1 : ℕ) : ℝ) = (V.N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hexp : V.N - 1 - 1 = V.N - 2 := by omega
  rw [hcast, hexp] at h
  refine (show HasDerivWithinAt (firstPriceBid V) _ (Icc 0 V.vbar) v from h).congr_deriv ?_
  simp only [firstPriceBid]
  field_simp
  ring

lemma fp_ident (hV : V.IsRegular) (hN : 2 ≤ V.N) {u : ℝ} (hu : u ∈ Icc 0 V.vbar) :
    firstPriceWinProb V u * (u - firstPriceBid V u) =
      ∫ s in (0 : ℝ)..u, firstPriceWinProb V s := by
  rcases hu.1.lt_or_eq with h | h
  · have hP := fp_Ppos V hV ⟨h, hu.2⟩
    unfold firstPriceBid
    field_simp
    ring
  · subst h
    simp [firstPriceWinProb, hV.2.1, zero_pow (show V.N - 1 ≠ 0 by omega)]

lemma fp_b (hV : V.IsRegular) (hN : 2 ≤ V.N) (v w : ℝ) (hv : v ∈ Icc 0 V.vbar)
    (hw : w ∈ Icc 0 V.vbar) :
    firstPriceWinProb V w * (v - firstPriceBid V w) ≤
      firstPriceWinProb V v * (v - firstPriceBid V v) := by
  have h0 : (0 : ℝ) ∈ Icc 0 V.vbar := ⟨le_rfl, hV.1.le⟩
  have e1 : firstPriceWinProb V w * (v - firstPriceBid V w) =
      firstPriceWinProb V w * (v - w) + ∫ s in (0 : ℝ)..w, firstPriceWinProb V s := by
    rw [← fp_ident V hV hN hw]; ring
  rw [e1, fp_ident V hV hN hv]
  have hsub : (∫ s in (0 : ℝ)..v, firstPriceWinProb V s) -
      ∫ s in (0 : ℝ)..w, firstPriceWinProb V s = ∫ s in w..v, firstPriceWinProb V s :=
    intervalIntegral.integral_interval_sub_left (fp_int V hV h0 hv) (fp_int V hV h0 hw)
  suffices h : firstPriceWinProb V w * (v - w) ≤ ∫ s in w..v, firstPriceWinProb V s by linarith
  rcases le_total w v with hwv | hvw
  · have := intervalIntegral.integral_mono_on hwv intervalIntegrable_const (fp_int V hV hw hv)
      (fun x hx => fp_Pmono V hV hw ⟨hw.1.trans hx.1, hx.2.trans hv.2⟩ hx.1)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  · have := intervalIntegral.integral_mono_on hvw (fp_int V hV hv hw) intervalIntegrable_const
      (fun x hx => fp_Pmono V hV ⟨hv.1.trans hx.1, hx.2.trans hw.2⟩ hw hx.2)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    rw [intervalIntegral.integral_symm]
    linarith

lemma fp_c (hV : V.IsRegular) (v : ℝ) (hv : v ∈ Ioc 0 V.vbar) : firstPriceBid V v < v := by
  have hvI := Ioc_subset_Icc_self hv
  have hP := fp_Ppos V hV hv
  have hpos : 0 < ∫ s in (0 : ℝ)..v, firstPriceWinProb V s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (fp_int V hV ⟨le_rfl, hV.1.le⟩ hvI)
      (fun x hx => fp_Ppos V hV ⟨hx.1, hx.2.le.trans hv.2⟩) hv.1
  unfold firstPriceBid
  have := div_pos hpos hP
  linarith

end RevenueManagement

open RevenueManagement

theorem solution (V : PrivateValues) (hV : V.IsRegular) (hN : 2 ≤ V.N) :
    (∀ v ∈ Set.Ioc 0 V.vbar, HasDerivWithinAt (firstPriceBid V)
        ((((V.N : ℝ) - 1) * V.F v ^ (V.N - 2) * V.f v / firstPriceWinProb V v) *
          (v - firstPriceBid V v)) (Set.Icc 0 V.vbar) v) ∧
    (∀ v ∈ Set.Icc 0 V.vbar, ∀ w ∈ Set.Icc 0 V.vbar,
      firstPriceWinProb V w * (v - firstPriceBid V w) ≤
        firstPriceWinProb V v * (v - firstPriceBid V v)) ∧
    (∀ v ∈ Set.Ioc 0 V.vbar, firstPriceBid V v < v) :=
  ⟨fun v hv => fp_a V hV hN v hv, fun v hv w hw => fp_b V hV hN v w hv hw,
    fun v hv => fp_c V hV v hv⟩
