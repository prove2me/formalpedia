-- Prove2me | solution 1 for ReciprocityTheory.Cheb.euler_exp_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:29.792943+00:00
-- url     : https://prove2.me/submissions/1acbd64d-583e-4eec-90ab-17f53d22def4

import Definitions.Def_ReciprocityTheory_Chebotarev_EulerFin
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerLim
import Theorems.Thm_ReciprocityTheory_Cheb_euler_hasProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {E : Type} [Field E] [NumberField E] (f : Ideal (𝓞 E) → ℂ) (hf1 : f 1 = 1)
    (hmul : ∀ a b : Ideal (𝓞 E), f (a * b) = f a * f b)
    (hsum : Summable (fun a : NZIdeal E => ‖f a.1‖)) (hlt : ∀ q : Prm E, ‖f q.asIdeal‖ < 1) :
    Complex.exp (∑' q : Prm E, -Complex.log (1 - f q.asIdeal)) = ∑' a : NZIdeal E, f a.1 := by
  have hinj : Function.Injective (fun q : Prm E => (⟨q.asIdeal, q.ne_bot⟩ : NZIdeal E)) := by
    intro q q' h
    exact IsDedekindDomain.HeightOneSpectrum.ext (congrArg Subtype.val h)
  have hs1 : Summable (fun q : Prm E => ‖f q.asIdeal‖) := by
    have h := hsum.comp_injective hinj
    exact h
  have hs2 : Summable (fun q : Prm E => -f q.asIdeal) := (Summable.of_norm hs1).neg
  have hs3 : Summable (fun q : Prm E => -Complex.log (1 - f q.asIdeal)) := by
    have := (Complex.summable_log_one_add_of_summable hs2).neg
    simp only [← sub_eq_add_neg] at this
    exact this
  have hP := hs3.hasSum.cexp
  have hne : ∀ q : Prm E, 1 - f q.asIdeal ≠ 0 := by
    intro q h
    have h1 : f q.asIdeal = 1 := (sub_eq_zero.mp h).symm
    have := hlt q
    rw [h1, norm_one] at this
    exact lt_irrefl _ this
  have hP' : HasProd (fun q : Prm E => (1 - f q.asIdeal)⁻¹)
      (Complex.exp (∑' q : Prm E, -Complex.log (1 - f q.asIdeal))) := by
    have e : (Complex.exp ∘ fun q : Prm E => -Complex.log (1 - f q.asIdeal)) =
        fun q : Prm E => (1 - f q.asIdeal)⁻¹ := by
      funext q
      rw [Function.comp_apply, Complex.exp_neg, Complex.exp_log (hne q)]
    rw [e] at hP
    exact hP
  exact hP'.unique (euler_hasProd f hf1 hmul hsum hlt)
end ReciprocityTheory.Cheb
