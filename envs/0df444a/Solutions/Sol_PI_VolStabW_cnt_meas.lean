-- Prove2me | solution 1 for PI.VolStabW.cnt_meas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:13:23.876879+00:00
-- url     : https://prove2.me/submissions/3d9b9afd-9819-4514-9e5e-870a374353a8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCntQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensCnt
import Theorems.Thm_PI_VolStabW_coe_hermSMul
import Theorems.Thm_PI_VolStabW_incl_mem
import Theorems.Thm_PI_VolStabW_int_iff
import Theorems.Thm_PI_VolStabW_measure_count
import Theorems.Thm_PI_VolStabW_mem_smulSub
import Theorems.Thm_PI_VolStabW_rho_eq_zero
import Theorems.Thm_PI_VolStabW_rho_sig
import Theorems.Thm_PI_VolStabW_rho_surj
import Theorems.Thm_PI_VolStabW_smul_char
import Theorems.Thm_PI_VolStabW_unifV_spec


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
  (hD : algebraMap F (Fv F v) A.D0 ∈ v.adicCompletionIntegers F)
variable {K : Type} [CommRing K] [Algebra (𝓞 F ⧸ v.asIdeal) K] (r : K)
  (hr : r * r = algebraMap _ K (red v (algebraMap F (Fv F v) A.D0)))
  (σ' : K ≃ₐ[𝓞 F ⧸ v.asIdeal] K) (hσr : σ' r = -r)
variable (hbij : Function.Bijective
  (fun p : (𝓞 F ⧸ v.asIdeal) × (𝓞 F ⧸ v.asIdeal) => algebraMap _ K p.1 + algebraMap _ K p.2 * r))
include hσr hbij
set_option maxHeartbeats 400000
namespace PI.VolStabW
theorem _root_.solution [Finite K] (hσ : ∀ x, σ (σ x) = x) {M a d : ℕ} [MeasurableAdd (Fin a → Fin M → Fv F v ⊗[F] E)] (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (T : Matrix (Fin a) (Fin a) E)
    (hT : ∀ i j, σ (T j i) = T i j) (b : Module.Basis (Fin d) F E)
    (hbc : ∀ j k, algebraMap F (Fv F v) (b.repr (A.c j) k) ∈ v.adicCompletionIntegers F)
    (hcb : ∀ k j, algebraMap F (Fv F v) (A.c.repr (b k) j) ∈ v.adicCompletionIntegers F)
    (hJi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (J p q) j) ∈ v.adicCompletionIntegers F)
    (hTi : ∀ p q j, algebraMap F (Fv F v) (A.c.repr (T p q) j) ∈ v.adicCompletionIntegers F)
    (hNm : MeasurableSet (lamF b v a M 0 : Set (Fin a → Fin M → Fv F v ⊗[F] E)))
    (μ : Measure (Fin a → Fin M → Fv F v ⊗[F] E)) [μ.IsAddLeftInvariant] :
    μ (latV b v ∩ gramH (Fv F v) σ hσ J hJ ⁻¹'
          {z | z - hermOf (Fv F v) σ T hT ∈ hF b v σ a 0}) =
        (Nat.card {X : Fin a → Fin M → K // ffGram (σ' : K →+* K)
          ((entL v A hD J hJi).map (rho v A hD r hr)) X = (entL v A hD T hTi).map (rho v A hD r hr)} : ENNReal) *
          μ (lamF b v a M 0) := by
  classical
  have rs := rho_sig v A hD r hr σ' hσr
  have rz := rho_eq_zero v A hD r hr hbij
  have rsu := rho_surj v A hD r hr hbij
  generalize rho v A hD r hr = ρ at rs rz rsu ⊢
  obtain ⟨rT, rT_eq⟩ : ∃ f : Fv F v ⊗[F] E → K, ∀ z (h : z ∈ lamC v A hD), f z = ρ ⟨z, h⟩ :=
    ⟨fun z => if h : z ∈ lamC v A hD then ρ ⟨z, h⟩ else 0, fun z h => dif_pos h⟩
  have memL : ∀ Y, Y ∈ latSub b v a M ↔ ∀ i p, Y i p ∈ lamC v A hD := by
    intro Y
    show (∀ i p k, _ ∈ _) ↔ _
    refine forall_congr' fun i => forall_congr' fun p => ?_
    rw [int_iff v b A.c hbc hcb, Fin.forall_fin_two]
    exact Iff.rfl
  have memN : ∀ Y, Y ∈ lamF b v a M 0 ↔
      ∀ i p, ∃ z', z' ∈ lamC v A hD ∧ unifV v • z' = Y i p := by
    intro Y
    rw [lamF, mem_smulSub, zero_add, pow_one]
    constructor
    · rintro ⟨Y', hY', rfl⟩ i p
      exact ⟨Y' i p, (memL Y').1 hY' i p, rfl⟩
    · intro h
      choose f hf1 hf2 using h
      exact ⟨f, (memL f).2 hf1, funext fun i => funext fun p => hf2 i p⟩
  have hsm : ∀ w : lamC v A hD,
      (∃ z', z' ∈ lamC v A hD ∧ unifV v • z' = (w : Fv F v ⊗[F] E)) ↔ ρ w = 0 := by
    intro w
    rw [smul_char v A hD, rz]
    exact ⟨fun h => h.2, fun h => ⟨w.2, h⟩⟩
  have hNL : lamF b v a M 0 ≤ latSub b v a M := by
    intro Y hY
    rw [memN] at hY
    rw [memL]
    intro i p
    obtain ⟨z', hz', e⟩ := hY i p
    rw [← e]
    exact ((smul_char v A hD _).1 ⟨z', hz', rfl⟩).1
  have hker : ∀ Y ∈ latSub b v a M, (fun i p => rT (Y i p)) = 0 ↔ Y ∈ lamF b v a M 0 := by
    intro Y hY
    rw [memN, funext_iff]
    refine forall_congr' fun i => ?_
    rw [funext_iff]
    refine forall_congr' fun p => ?_
    have h1 := (memL Y).1 hY i p
    rw [hsm ⟨Y i p, h1⟩]
    show rT (Y i p) = 0 ↔ _
    rw [rT_eq _ h1]
  have hadd : ∀ Y ∈ latSub b v a M, ∀ Y' ∈ latSub b v a M,
      (fun i p => rT ((Y + Y') i p)) = (fun i p => rT (Y i p)) + (fun i p => rT (Y' i p)) := by
    intro Y hY Y' hY'
    funext i p
    have h1 := (memL Y).1 hY i p
    have h2 := (memL Y').1 hY' i p
    show rT (Y i p + Y' i p) = rT (Y i p) + rT (Y' i p)
    rw [rT_eq _ (add_mem h1 h2), rT_eq _ h1, rT_eq _ h2, ← map_add]
    rfl
  have hsurj : ∀ W : Fin a → Fin M → K, ∃ Y ∈ latSub b v a M, (fun i p => rT (Y i p)) = W := by
    intro W
    choose g hg using fun i p => rsu (W i p)
    refine ⟨fun i p => (g i p : Fv F v ⊗[F] E), (memL _).2 fun i p => (g i p).2, ?_⟩
    funext i p
    show rT (g i p : Fv F v ⊗[F] E) = W i p
    rw [rT_eq _ (g i p).2]
    exact hg i p
  have rT_mul : ∀ z w, z ∈ lamC v A hD → w ∈ lamC v A hD → rT (z * w) = rT z * rT w := by
    intro z w hz hw
    rw [rT_eq _ (mul_mem hz hw), rT_eq _ hz, rT_eq _ hw, ← map_mul]
    rfl
  have rT_sub : ∀ z w, z ∈ lamC v A hD → w ∈ lamC v A hD → rT (z - w) = rT z - rT w := by
    intro z w hz hw
    rw [rT_eq _ (sub_mem hz hw), rT_eq _ hz, rT_eq _ hw, ← map_sub]
    rfl
  have rT_sig : ∀ z, z ∈ lamC v A hD → rT (sigR (Fv F v) σ z) = σ' (rT z) := by
    intro z hz
    rw [rT_eq _ (sig_mem v A hD hz), rT_eq _ hz, ← rs ⟨z, hz⟩]
    rfl
  have rT_sum : ∀ (s : Finset (Fin M)) (f : Fin M → Fv F v ⊗[F] E),
      (∀ p, f p ∈ lamC v A hD) → rT (∑ p ∈ s, f p) = ∑ p ∈ s, rT (f p) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, rT_eq _ (zero_mem _), ← map_zero ρ]
      rfl
    | insert p s hp ih =>
      have hs : ∑ q ∈ s, f q ∈ lamC v A hD := sum_mem fun q _ => hf q
      rw [Finset.sum_insert hp, Finset.sum_insert hp, ← ih, rT_eq _ (add_mem (hf p) hs),
        rT_eq _ (hf p), rT_eq _ hs, ← map_add]
      rfl
  have hsm' : ∀ z, z ∈ lamC v A hD →
      ((∃ z', z' ∈ lamC v A hD ∧ unifV v • z' = z) ↔ rT z = 0) := by
    intro z hz
    rw [rT_eq _ hz]
    exact hsm ⟨z, hz⟩
  have hentry : ∀ Y, (∀ i p, Y i p ∈ lamC v A hD) → ∀ i j,
      ((gramH (Fv F v) σ hσ J hJ Y : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) ∈ lamC v A hD ∧
      rT ((gramH (Fv F v) σ hσ J hJ Y : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) =
        ffGram (σ' : K →+* K) ((entL v A hD J hJi).map ρ) (fun i p => rT (Y i p)) i j := by
    intro Y hY i j
    have e1 : ((gramH (Fv F v) σ hσ J hJ Y : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) =
        ∑ p, ∑ q, sigR (Fv F v) σ (Y i p) * inclR (Fv F v) (J p q) * Y j q := rfl
    have hmem : ∀ p q, sigR (Fv F v) σ (Y i p) * inclR (Fv F v) (J p q) * Y j q ∈ lamC v A hD :=
      fun p q => mul_mem (mul_mem (sig_mem v A hD (hY i p)) (incl_mem v A hD _ (hJi p q))) (hY j q)
    rw [e1]
    refine ⟨sum_mem fun p _ => sum_mem fun q _ => hmem p q, ?_⟩
    rw [rT_sum _ _ fun p => sum_mem fun q _ => hmem p q]
    show _ = ∑ p, ∑ q, (σ' : K →+* K) (rT (Y i p)) * ρ (entL v A hD J hJi p q) * rT (Y j q)
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [rT_sum _ _ fun q => hmem p q]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [rT_mul _ _ (mul_mem (sig_mem v A hD (hY i p)) (incl_mem v A hD _ (hJi p q))) (hY j q),
      rT_mul _ _ (sig_mem v A hD (hY i p)) (incl_mem v A hD _ (hJi p q)), rT_sig _ (hY i p),
      rT_eq _ (incl_mem v A hD _ (hJi p q))]
    rfl
  have hFm : ∀ S : HermR (Fv F v) σ a, S ∈ hF b v σ a 0 ↔
      ∀ i j, ∃ z', z' ∈ lamC v A hD ∧
        unifV v • z' = (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j := by
    intro S
    rw [hF, mem_smulSub, zero_add, pow_one]
    constructor
    · rintro ⟨S', hS', rfl⟩ i j
      have hS'' : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((S' : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈ v.adicCompletionIntegers F := hS'
      have hc := (int_iff v b A.c hbc hcb _).1 (hS'' i j)
      exact ⟨(S' : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j, ⟨hc 0, hc 1⟩, rfl⟩
    · intro h
      choose f hf1 hf2 using h
      refine ⟨(unifV v)⁻¹ • S, ?_, ?_⟩
      · intro i j
        show ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr
          ((((unifV v)⁻¹ • S : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k ∈ _
        rw [coe_hermSMul, Matrix.smul_apply, ← hf2 i j, smul_smul,
          inv_mul_cancel₀ (unifV_spec v).1, one_smul]
        exact (int_iff v b A.c hbc hcb _).2 (Fin.forall_fin_two.2 (hf1 i j))
      · apply Subtype.ext
        rw [coe_hermSMul, coe_hermSMul, smul_smul, mul_inv_cancel₀ (unifV_spec v).1, one_smul]
  have hset : latV b v ∩ gramH (Fv F v) σ hσ J hJ ⁻¹'
        {z | z - hermOf (Fv F v) σ T hT ∈ hF b v σ a 0} =
      {Y | Y ∈ latSub b v a M ∧ (fun i p => rT (Y i p)) ∈
        {X | ffGram (σ' : K →+* K) ((entL v A hD J hJi).map ρ) X = (entL v A hD T hTi).map ρ}} := by
    ext Y
    show (Y ∈ latSub b v a M ∧ _) ↔ (Y ∈ latSub b v a M ∧ _)
    refine and_congr_right fun hY => ?_
    have hY' := (memL Y).1 hY
    show _ ∈ hF b v σ a 0 ↔ ffGram (σ' : K →+* K) ((entL v A hD J hJi).map ρ) (fun i p => rT (Y i p)) =
      (entL v A hD T hTi).map ρ
    rw [hFm, ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    obtain ⟨hg1, hg2⟩ := hentry Y hY' i j
    have hTm := incl_mem v A hD _ (hTi i j)
    have e : ((gramH (Fv F v) σ hσ J hJ Y - hermOf (Fv F v) σ T hT : HermR (Fv F v) σ a) :
        Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
        (gramH (Fv F v) σ hσ J hJ Y : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j -
          inclR (Fv F v) (T i j) := rfl
    rw [e, hsm' _ (sub_mem hg1 hTm), rT_sub _ _ hg1 hTm, sub_eq_zero, hg2, rT_eq _ hTm]
    exact Iff.rfl
  rw [hset, measure_count μ (latSub b v a M) (lamF b v a M 0) hNL hNm (fun Y i p => rT (Y i p))
    hadd hker hsurj]
  rfl
end PI.VolStabW
