-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.eq_of_mem_parPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:28:34.185044+00:00
-- url     : https://prove2.me/submissions/71c69503-945a-4ef7-9720-1dc25e492dae

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Theorems.Thm_ReciprocityTheory_AnForm_R_isDomain_of_isRegularLocalRing
import Theorems.Thm_ReciprocityTheory_AnForm_R_prime_of_regular_params
import Theorems.Thm_ReciprocityTheory_AnForm_R_regular_params_spec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S] {p : Ideal A} [p.IsPrime]
  [IsLocalization.AtPrime S p] [IsRegularLocalRing S] {n : ℕ} {f : Fin n → A}
variable (S)
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution (hrsp : FinalTheorems.Rsp S n (fun i => algebraMap A S (f i))) {i j : Fin n}
    (h : f j ∈ parPrime (S := S) f i) : j = i := by
  by_contra hji
  have : IsDomain S := isDomain_of_isRegularLocalRing
  have hpi := prime_of_regular_params _ hrsp.1 hrsp.2 i
  have hpj := prime_of_regular_params _ hrsp.1 hrsp.2 j
  have hd : algebraMap A S (f i) ∣ algebraMap A S (f j) :=
    Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp h)
  have hass : Associated (algebraMap A S (f i)) (algebraMap A S (f j)) :=
    hpi.associated_of_dvd hpj hd
  exact (regular_params_spec _ hrsp.1 hrsp.2).2 i j (Ne.symm hji) hass
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
