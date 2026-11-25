-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_LocalizeSubvar_quotientMap_surjective_89fc8fe2747e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:14:05.825988+00:00
-- url     : https://prove2.me/submissions/0ba26126-807b-40ec-bd7b-5f318b85893e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_LocalizeSubvarSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLocalizeSubvar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
namespace LocalizeSubvar
theorem _root_.solution (S : Type) [CommRing S] (𝔪 : Ideal S) [𝔪.IsMaximal]
    (O : Type) [CommRing O] [Algebra S O] [IsLocalization.AtPrime O 𝔪] (N : ℕ)
    (pp' : Ideal (Kleiman.Poly O N))
    (hle : (𝔪.map (algebraMap S O)).map (C : O →+* Kleiman.Poly O N) ≤ pp') :
    Function.Surjective (Ideal.quotientMap pp'
      (MvPolynomial.map (algebraMap S O) : Kleiman.Poly S N →+* Kleiman.Poly O N) le_rfl) := by
  set φ := Ideal.quotientMap pp'
    (MvPolynomial.map (algebraMap S O) : Kleiman.Poly S N →+* Kleiman.Poly O N) le_rfl with hφ
  have key : ∀ q : Kleiman.Poly O N, Ideal.Quotient.mk pp' q ∈ φ.range := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C o =>
      obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl o
      obtain ⟨y, i, hi, hyi⟩ := Ideal.IsMaximal.exists_inv (inferInstance : 𝔪.IsMaximal) t.2
      refine ⟨Ideal.Quotient.mk _ (C (s * y)), ?_⟩
      rw [Ideal.quotientMap_mk, map_C, Ideal.Quotient.eq]
      set v : O := IsLocalization.mk' O (1 : S) t
      have h1 : algebraMap S O t * v = 1 := by rw [IsLocalization.mk'_spec', map_one]
      have h2 : algebraMap S O y * algebraMap S O t + algebraMap S O i = 1 := by
        rw [← map_mul, ← map_add, hyi, map_one]
      have ho : IsLocalization.mk' O s t = algebraMap S O s * v := IsLocalization.mk'_eq_mul_mk'_one s t
      have hd : algebraMap S O (s * y) - IsLocalization.mk' O s t =
          -(algebraMap S O i * (algebraMap S O s * v)) := by
        rw [ho, map_mul]
        linear_combination (-(algebraMap S O y * algebraMap S O s)) * h1 +
          (algebraMap S O s * v) * h2
      rw [← map_sub, hd, map_neg, map_mul]
      refine neg_mem (Ideal.mul_mem_right _ _ (hle ?_))
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hi)
    | add p q hp hq => rw [map_add]; exact Subring.add_mem _ hp hq
    | mul_X p j hp =>
      rw [map_mul]
      refine Subring.mul_mem _ hp ⟨Ideal.Quotient.mk _ (X j), ?_⟩
      rw [Ideal.quotientMap_mk, map_X]
  intro z
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact key q
end LocalizeSubvar
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
