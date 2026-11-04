-- Prove2me | solution 1 for ThreeSum.LightCyclic.fold_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:19:48.741388+00:00
-- url     : https://prove2.me/submissions/7b6d833f-e15f-4236-b42d-b58536016931

import Definitions.Def_Submission_ThreeSum_CyclicFold
import Definitions.Def_Submission_ThreeSum_KaratsubaInterface
import Definitions.Def_Submission_ThreeSum_LightCyclic
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_padTo
import Theorems.Thm_ThreeSum_CyclicFold_asPolynomial_replicate_zero
import Theorems.Thm_ThreeSum_CyclicFold_fold_product
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Definitions.Def_WeightedCache3SUM_Alias_fb87d121ace1c0e2
import Definitions.Def_WeightedCache3SUM_Alias_a7357418fd94c5da
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.CyclicFold.asPolynomial_replicate_zero
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LightKaratsuba.window_sub



set_option autoImplicit false
open ThreeSum ThreeSum.LightCyclic
open Light Karatsuba CyclicFold LightKaratsuba
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCyclic
theorem _root_.solution {pLinear : ℕ} (hLinear : P[pLinear]? = some LightArray.linearBody)
    {μ : ℕ → ℤ} {src dst n p U : ℕ} {as bs : List ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ n)
    (hsrc : src + 2*n ≤ lim.space) (hdst : dst + p ≤ lim.space)
    (hsep : Apart src (2*n) dst p)
    (ha : as.length ≤ p) (hb : bs.length ≤ p)
    (hA : CoeffBound as (U : ℤ)) (hB : CoeffBound bs (U : ℤ))
    (hprod : ProductAt μ src n (padTo n as) (padTo n bs))
    (hword : 4 * (p : ℤ) * (U : ℤ)^2 ≤ lim.word) :
    Meets lim P pLinear d [src, src+p, dst, p, 1] μ (LightArray.linearTime p)
      fun _ μ' => (∀ r < p, μ' (dst+r) = cyclic p as bs r) ∧
        SameOutside μ μ' dst p := by
  have hfirst (r : ℕ) (hr : r < p) :
      μ (src+r) = (asPolynomial as * asPolynomial bs).coeff r := by
    simpa only [asPolynomial_padTo] using hprod r (by omega)
  have hsecond (r : ℕ) (hr : r < p) :
      μ (src+p+r) = (asPolynomial as * asPolynomial bs).coeff (r+p) := by
    simpa only [asPolynomial_padTo, Nat.add_assoc, Nat.add_comm p r] using
      hprod (r+p) (by omega)
  have hc (r : ℕ) :
      |(asPolynomial as * asPolynomial bs).coeff r| ≤ (2*p*U^2 : ℕ) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      product_coeff_bound ha hb hA hB r
  have h := LightArray.linear_bounded_meets (d := d) (μ := μ)
    (srcA := src) (srcB := src+p) (dst := dst) (n := p) (U := 2*p*U^2) (c := 1)
    hLinear hw (by omega) (by omega) hdst (Or.inr (by omega)) (Or.inr (by omega))
    (by norm_num) (by push_cast; nlinarith) (by
      intro r hr
      rw [hfirst r hr, hsecond r hr]
      exact ⟨hc r, hc (r+p)⟩)
  apply h.mono le_rfl
  intro res μ' hpost
  refine ⟨?_, hpost.2⟩
  intro r hr
  rw [hpost.1 r hr, one_mul, hfirst r hr, hsecond r hr]
  exact fold_product as bs p r ha hb hr
end ThreeSum.LightCyclic
