-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitD_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:58:25.124409+00:00
-- url     : https://prove2.me/submissions/549b6fc9-67f3-4971-95e2-ecf2ef81d2c9

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitD
import Theorems.Thm_ReciprocityTheory_Cheb_splitD_natCast_not_mem
import Theorems.Thm_ReciprocityTheory_Cheb_under_asIdeal


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
theorem _root_.solution (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (q : Prm E)
    (P : Prm (CyclotomicField l E)) (hP : under P = q) (hl : ¬ l ∣ Nrm q) :
    ∃ σ : CyclotomicField l E ≃ₐ[E] CyclotomicField l E,
      σ (IsCyclotomicExtension.zeta l E (CyclotomicField l E)) =
        IsCyclotomicExtension.zeta l E (CyclotomicField l E) ^ Nrm q ∧
      ∀ x : 𝓞 (CyclotomicField l E), ∃ y : 𝓞 (CyclotomicField l E),
        (y : CyclotomicField l E) = σ (x : CyclotomicField l E) ∧ y - x ^ Nrm q ∈ P.asIdeal := by
  have : IsGalois E (CyclotomicField l E) := IsCyclotomicExtension.isGalois {l} E _
  have : Algebra.IsInvariant (𝓞 E) (𝓞 (CyclotomicField l E))
      (𝓞 (CyclotomicField l E) ≃ₐ[𝓞 E] 𝓞 (CyclotomicField l E)) :=
    Algebra.isInvariant_of_isGalois' (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))
  have : Finite (𝓞 (CyclotomicField l E) ≃ₐ[𝓞 E] 𝓞 (CyclotomicField l E)) :=
    Finite.of_equiv _ (galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).toEquiv
  have : P.asIdeal.IsPrime := P.isPrime
  have : Finite (𝓞 (CyclotomicField l E) ⧸ P.asIdeal) :=
    (Ideal.absNorm_ne_zero_iff P.asIdeal).1 (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot)
  obtain ⟨τ, hτ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E)
    (𝓞 (CyclotomicField l E) ≃ₐ[𝓞 E] 𝓞 (CyclotomicField l E)) P.asIdeal
  have hcard : Nat.card (𝓞 E ⧸ P.asIdeal.under (𝓞 E)) = Nrm q := by
    rw [Nrm, ← hP, under_asIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hσ : ∀ x : 𝓞 (CyclotomicField l E),
      ((τ x : 𝓞 (CyclotomicField l E)) : CyclotomicField l E) =
        (galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).symm τ
          (x : CyclotomicField l E) := by
    intro x
    have := algebraMap_galRestrict_apply (𝓞 E)
      ((galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).symm τ) x
    simpa only [MulEquiv.apply_symm_apply] using this
  have hfr : ∀ x : 𝓞 (CyclotomicField l E), τ x - x ^ Nrm q ∈ P.asIdeal := by
    intro x
    have := hτ x
    rw [hcard] at this
    exact this
  refine ⟨(galRestrict (𝓞 E) E (CyclotomicField l E) (𝓞 (CyclotomicField l E))).symm τ, ?_,
    fun x => ⟨τ x, hσ x, hfr x⟩⟩
  have hz := IsCyclotomicExtension.zeta_spec l E (CyclotomicField l E)
  have hlP : ((l : ℕ) : 𝓞 (CyclotomicField l E)) ∉ P.asIdeal := by
    intro h
    apply splitD_natCast_not_mem E l q hl
    rw [← hP, under_asIdeal, Ideal.mem_comap, map_natCast]
    exact h
  have h1 := hτ.apply_of_pow_eq_one (ζ := hz.toInteger) (m := l) hz.toInteger_isPrimitiveRoot.pow_eq_one hlP
  rw [hcard] at h1
  have h2 : ((τ hz.toInteger : 𝓞 (CyclotomicField l E)) : CyclotomicField l E) =
      ((hz.toInteger ^ Nrm q : 𝓞 (CyclotomicField l E)) : CyclotomicField l E) := congrArg _ h1
  rw [hσ] at h2
  push_cast at h2
  exact h2
end ReciprocityTheory.Cheb
