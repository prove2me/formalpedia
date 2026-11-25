-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitE_autEquivPow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:46:10.117585+00:00
-- url     : https://prove2.me/submissions/8b8038ae-7e9a-4359-aa87-7e7d79f47001

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitEA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (hirr : Irreducible (Polynomial.cyclotomic l E))
    (σ : CyclotomicField l E ≃ₐ[E] CyclotomicField l E) (m : ℕ)
    (hσ : σ (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) =
      IsCyclotomicExtension.zeta l E (CyclotomicField l E) ^ m) :
    ((IsCyclotomicExtension.autEquivPow (CyclotomicField l E) hirr σ : (ZMod l)ˣ) : ZMod l) = (m : ZMod l) := by
  have hζ := IsCyclotomicExtension.zeta_spec l E (CyclotomicField l E)
  rw [IsCyclotomicExtension.autEquivPow_apply]
  have h1 := hζ.autToPow_spec E σ
  rw [hσ] at h1
  have hfin : IsOfFinOrder (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨l, (Fact.out : l.Prime).pos, hζ.pow_eq_one⟩
  have h2 := hfin.pow_eq_pow_iff_modEq.1 h1
  rw [← hζ.eq_orderOf] at h2
  change (((hζ.autToPow E σ : (ZMod l)ˣ) : ZMod l)) = _
  rw [← ZMod.natCast_zmod_val ((hζ.autToPow E σ : (ZMod l)ˣ) : ZMod l)]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h2
end ReciprocityTheory.Cheb
