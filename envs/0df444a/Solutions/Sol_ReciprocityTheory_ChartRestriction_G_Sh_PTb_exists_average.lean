-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.exists_average
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:14:28.475659+00:00
-- url     : https://prove2.me/submissions/5c155a36-5ff5-4353-a132-95123e86748e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_CardToMultisetEqDegree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_GeomSumRoot
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_geom_sum_root
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_coeff_expand_rescale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_dvd_of_lgCurve_low
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_expC_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_rescale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isCurve_sumF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_expC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_rescale
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_lgCurve_sumF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution (G : LogFGL v d) {p : ℕ} (hp : p.Prime) {ζ : C}
    (hζ : IsPrimitiveRoot ζ p) {ga : Fin d → PowerSeries C} (hga : IsCurve v ga) :
    ∃ δ : Fin d → PowerSeries C, IsCurve v δ ∧ ∀ c j, PowerSeries.coeff j (G.lgCurve δ c) =
      (p : C) * PowerSeries.coeff (p * j) (G.lgCurve ga c) := by
  classical
  have hp0 : p ≠ 0 := hp.ne_zero
  have h0 : ∀ b, PowerSeries.constantCoeff (ga b) = 0 := fun b => (hga b).1
  have hζv : ∀ j : ℕ, IsIntV v (ζ ^ j) := fun j => by
    unfold IsIntV
    rw [v_eq_zero_of_pow_eq_one (v := v) hp0
      (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])]

  obtain ⟨g, hgdef⟩ : ∃ g : Fin p → Fin d → PowerSeries C,
      ∀ u, g u = rescaleCurve (ζ ^ (u : ℕ)) ga := ⟨fun u => rescaleCurve (ζ ^ (u : ℕ)) ga, fun u => rfl⟩
  have hg : ∀ u, IsCurve v (g u) := fun u => by
    rw [hgdef]
    exact isCurve_rescale (hζv u) hga
  obtain ⟨ε, hεdef⟩ : ∃ ε : Fin d → PowerSeries C, ε = G.sumF g := ⟨_, rfl⟩
  have hε : IsCurve v ε := by
    rw [hεdef]
    exact isCurve_sumF G g hg
  have hεc : ∀ b, PowerSeries.constantCoeff (ε b) = 0 := fun b => (hε b).1
  have hsum : ∀ m : ℕ, ∑ u : Fin p, (ζ ^ (u : ℕ)) ^ m = if p ∣ m then (p : C) else 0 := by
    intro m
    rw [← geom_sum_root hζ m, Fin.sum_univ_eq_sum_range (fun j => (ζ ^ j) ^ m) p]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hlgε : ∀ c m, PowerSeries.coeff m (G.lgCurve ε c) =
      if p ∣ m then (p : C) * PowerSeries.coeff m (G.lgCurve ga c) else 0 := by
    intro c m
    rw [hεdef, lgCurve_sumF G g hg c, map_sum]
    simp only [hgdef, lgCurve_rescale G _ h0, PowerSeries.coeff_rescale]
    rw [← Finset.sum_mul, hsum m]
    split_ifs <;> simp

  have hinv : ∀ a, rescaleCurve ζ ε a = ε a := by
    have hζ1 : IsIntV v ζ := by simpa using hζv 1
    have hεζc : ∀ b, PowerSeries.constantCoeff (rescaleCurve ζ ε b) = 0 :=
      fun b => (isCurve_rescale hζ1 hε b).1
    intro a
    have hdvd : ∀ N, (PowerSeries.X : PowerSeries C) ^ N ∣ rescaleCurve ζ ε a - ε a := fun N =>
      dvd_of_lgCurve_low G hεζc hεc N (fun a' j _ => by
        rw [lgCurve_rescale G ζ hεc, PowerSeries.coeff_rescale, hlgε]
        split_ifs with h
        · obtain ⟨k, rfl⟩ := h
          rw [pow_mul, hζ.pow_eq_one, one_pow, one_mul]
        · rw [mul_zero]) a
    rw [← sub_eq_zero]
    ext m
    have := (PowerSeries.X_pow_dvd_iff.mp (hdvd (m + 1))) m (Nat.lt_succ_self m)
    simpa using this
  have hoff : ∀ a m, ¬ p ∣ m → PowerSeries.coeff m (ε a) = 0 := by
    intro a m hm
    have h1 := congrArg (PowerSeries.coeff m) (hinv a)
    simp only [rescaleCurve, PowerSeries.coeff_rescale] at h1
    have hne : ζ ^ m ≠ 1 := fun h => hm (hζ.dvd_of_pow_eq_one m h)
    have h2 : (ζ ^ m - 1) * PowerSeries.coeff m (ε a) = 0 := by
      rw [sub_mul, one_mul, h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

  obtain ⟨δ, hδdef⟩ : ∃ δ : Fin d → PowerSeries C,
      ∀ a, δ a = PowerSeries.mk fun j => PowerSeries.coeff (p * j) (ε a) :=
    ⟨fun a => PowerSeries.mk fun j => PowerSeries.coeff (p * j) (ε a), fun a => rfl⟩
  have hexpand : ∀ (f : PowerSeries C) (m : ℕ), PowerSeries.coeff m (PowerSeries.expand p hp0 f) =
      if p ∣ m then PowerSeries.coeff (m / p) f else 0 := by
    intro f m
    have h := coeff_expand_rescale p hp0 1 f m
    rw [PowerSeries.rescale_one, RingHom.id_apply] at h
    rw [h]
    split_ifs <;> simp
  have hexp : ∀ a, PowerSeries.expand p hp0 (δ a) = ε a := by
    intro a
    ext m
    rw [hexpand]
    split_ifs with h
    · rw [hδdef, PowerSeries.coeff_mk, Nat.mul_div_cancel' h]
    · exact (hoff a m h).symm
  have hδ : IsCurve v δ := fun a => by
    refine ⟨?_, fun j => ?_⟩
    · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hδdef, PowerSeries.coeff_mk, mul_zero,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hεc a
    · rw [hδdef, PowerSeries.coeff_mk]
      exact (hε a).2 (p * j)
  have hεδ : expC p δ = ε := funext fun a => by
    rw [expC_apply hp0]
    exact hexp a
  refine ⟨δ, hδ, fun c j => ?_⟩
  have h1 := lgCurve_expC G hp0 (fun b => (hδ b).1) c
  rw [hεδ] at h1
  have h2 := congrArg (PowerSeries.coeff (p * j)) h1
  rw [hlgε, if_pos (dvd_mul_right p j), hexpand, if_pos (dvd_mul_right p j),
    Nat.mul_div_cancel_left j hp.pos] at h2
  exact h2.symm
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
