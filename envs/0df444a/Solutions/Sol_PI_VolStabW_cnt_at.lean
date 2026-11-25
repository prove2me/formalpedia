-- Prove2me | solution 1 for PI.VolStabW.cnt_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:48:04.645073+00:00
-- url     : https://prove2.me/submissions/94418229-24c8-405a-85b2-fee7cd531851

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCnt
import Theorems.Thm_PI_VolStabW_two_ne_zero_k
import Theorems.Thm_PI_VolStabW_cnt_herm
import Theorems.Thm_PI_VolStabW_cnt_unit
import Theorems.Thm_PI_VolStabW_cnt_meas
import Theorems.Thm_PI_VolStabW_exists_quadAlg
import Theorems.Thm_PI_VolStabW_red_eq_zero_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {σ : E →ₐ[F] E} (A : AntiB F E σ)
namespace PI.VolStabW
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) {M a d : ℕ} [MeasurableAdd (Fin a → Fin M → Fv F v ⊗[F] E)] (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (T : Matrix (Fin a) (Fin a) E)
    (hT : ∀ i j, σ (T j i) = T i j) (b : Module.Basis (Fin d) F E)
    (hbc : ∀ j k, algebraMap F (Fv F v) (b.repr (A.c j) k) ∈ v.adicCompletionIntegers F)
    (hcb : ∀ k j, algebraMap F (Fv F v) (A.c.repr (b k) j) ∈ v.adicCompletionIntegers F)
    (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)
    (hDu : Valued.v (algebraMap F (Fv F v) A.D0) = 1)
    (h2 : Valued.v (algebraMap F (Fv F v) 2) = 1)
    (hJi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (J p q) j) ∈ v.adicCompletionIntegers F)
    (hTi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (T p q) j) ∈ v.adicCompletionIntegers F)
    (hNm : MeasurableSet (lamF b v a M 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)))
    (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) [μ.IsAddLeftInvariant] :
    ∃ (k K : Type) (_ : Field k) (_ : Finite k) (_ : CommRing K) (_ : Algebra k K)
      (σ' : K ≃ₐ[k] K) (J' : Matrix (Fin M) (Fin M) K) (T' : Matrix (Fin a) (Fin a) K),
      IsQuadInv k K σ' ∧ (2 : k) ≠ 0 ∧ (∀ i j, σ' (J' j i) = J' i j) ∧
      (∀ u : E, J.det * u = 1 →
        (∀ j, algebraMap F (Fv F v) (A.c.repr u j) ∈ v.adicCompletionIntegers F) →
          IsUnit J'.det) ∧
      (∀ i j, σ' (T' j i) = T' i j) ∧
      (∀ u : E, T.det * u = 1 →
        (∀ j, algebraMap F (Fv F v) (A.c.repr u j) ∈ v.adicCompletionIntegers F) →
          IsUnit T'.det) ∧
      Nat.card k = Nat.card (𝓞 F ⧸ v.asIdeal) ∧
      μ (latV b v ∩ gramH (Fv F v) σ hσ J hJ ⁻¹'
          {z | z - hermOf (Fv F v) σ T hT ∈ hF b v σ a 0}) =
        (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K) J' X = T'} : ENNReal) *
          μ (lamF b v a M 0) := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  let fk : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  have h2k := two_ne_zero_k v h2
  have hDk : red v (algebraMap F (Fv F v) A.D0) ≠ 0 := by
    rw [Ne, red_eq_zero_iff v hD, hDu]; exact lt_irrefl 1
  obtain ⟨K, iK, iA, σ', r, hQ, hr, hσr, hbij⟩ := exists_quadAlg (𝓞 F ⧸ v.asIdeal) h2k _ hDk
  have : Finite K := Finite.of_surjective _ hbij.2
  exact ⟨𝓞 F ⧸ v.asIdeal, K, fk, hfin, iK, iA, σ', (entL v A hD J hJi).map (rho v A hD r hr),
    (entL v A hD T hTi).map (rho v A hD r hr), hQ, h2k,
    cnt_herm v A hD r hr σ' hσr J hJ hJi, fun u hu hui => cnt_unit v A hD r hr J hJi u hu hui,
    cnt_herm v A hD r hr σ' hσr T hT hTi, fun u hu hui => cnt_unit v A hD r hr T hTi u hu hui, rfl,
    cnt_meas v A hD r hr σ' hσr hbij hσ J hJ T hT b hbc hcb hJi hTi hNm μ⟩
end PI.VolStabW
