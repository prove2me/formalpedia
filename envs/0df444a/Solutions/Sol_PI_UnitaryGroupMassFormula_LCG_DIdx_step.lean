-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.LCG.DIdx.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:07:33.855364+00:00
-- url     : https://prove2.me/submissions/0f96bec9-a416-4eb4-9897-6046425cf505

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDual
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DIdx_absNorm_eq_index
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DIdx_quot_le
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DIdx_dualL_anti
import Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DIdx_smul_dot
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.DIdx
namespace PI.UnitaryGroupMassFormula.LCG.DIdx
theorem _root_.solution (K : Type) [Field K] [NumberField K] (k : ℕ) (X Y : Submodule (𝓞 K) (Fin k → K)) (hXY : X ≤ Y)
    (hne : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) (x : Fin k → K) (hxY : x ∈ Y) :
    (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≠ 0 ∧
    (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≤
      X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by
  have hX1Y : X ⊔ Submodule.span (𝓞 K) {x} ≤ Y :=
    sup_le hXY ((Submodule.span_singleton_le_iff_mem _ _).mpr hxY)
  have hxX1 : x ∈ X ⊔ Submodule.span (𝓞 K) {x} :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hneX1 : X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup ≠ 0 := fun h =>
    hne (AddSubgroup.relIndex_eq_zero_of_le_right ((Submodule.toAddSubgroup_le _ _).mpr hX1Y) h)

  let g : 𝓞 K →+ (Fin k → K) := AddMonoidHom.mk' (fun c => c • x) (fun c c' => add_smul c c' x)
  have e1 : (aI X x).toAddSubgroup = X.toAddSubgroup.comap g := by
    ext c
    exact Iff.rfl
  have hrange : g.range ≤ (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by
    rintro _ ⟨c, rfl⟩
    exact (X ⊔ Submodule.span (𝓞 K) {x}).smul_mem c hxX1
  have hN : Ideal.absNorm (aI X x) = X.toAddSubgroup.relIndex g.range := by
    rw [absNorm_eq_index, e1, AddSubgroup.index_comap]
  have hNne : Ideal.absNorm (aI X x) ≠ 0 := by
    rw [hN]
    exact fun h => hneX1 (AddSubgroup.relIndex_eq_zero_of_le_right hrange h)
  have hNle : Ideal.absNorm (aI X x) ≤ X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by
    rw [hN]
    exact AddSubgroup.relIndex_le_of_le_right hrange hneX1
  have h𝔞 : aI X x ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hNne
    exact hNne rfl
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔞
  have hax : a • x ∈ X := ha
  obtain ⟨hle, hq0, hqle⟩ := quot_le K (aI X x) h𝔞 a ha0

  let ψ : (Fin k → K) →+ K := AddMonoidHom.mk' (fun t => algebraMap (𝓞 K) K a * (x ⬝ᵥ t))
    (fun t t' => by simp only [dotProduct_add, mul_add])
  let mO : 𝓞 K →+ K := (algebraMap (𝓞 K) K).toAddMonoidHom
  have hinj : Function.Injective mO := IsFractionRing.injective (𝓞 K) K
  have ha0K : algebraMap (𝓞 K) K a ≠ 0 := fun h => ha0 (hinj (h.trans (map_zero _).symm))
  have claim1 : (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup =
      ((Ideal.span {a}).toAddSubgroup.map mO).comap ψ ⊓ (dualL X).toAddSubgroup := by
    ext t
    constructor
    · intro ht
      refine ⟨?_, dualL_anti le_sup_left ht⟩
      obtain ⟨o, ho⟩ := ht x hxX1
      refine ⟨a * o, Ideal.mul_mem_right o _ (Ideal.mem_span_singleton_self a), ?_⟩
      show algebraMap (𝓞 K) K (a * o) = algebraMap (𝓞 K) K a * (x ⬝ᵥ t)
      rw [map_mul, ho]
    · rintro ⟨⟨r, hr, hrt⟩, htX⟩
      obtain ⟨o, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      have hrt' : algebraMap (𝓞 K) K a * algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * (x ⬝ᵥ t) := by
        rw [← map_mul, mul_comm a o]
        exact hrt
      have hxt : x ⬝ᵥ t = algebraMap (𝓞 K) K o := (mul_left_cancel₀ ha0K hrt').symm
      intro s hs
      obtain ⟨s0, hs0, s1, hs1, rfl⟩ := Submodule.mem_sup.mp hs
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hs1
      rw [add_dotProduct, smul_dot, hxt, ← map_mul]
      exact add_mem (htX s0 hs0) ⟨c * o, rfl⟩
  have claim2 : (dualL X).toAddSubgroup.map ψ ≤ (qI (aI X x) a).toAddSubgroup.map mO := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨o, ho⟩ := (show t ∈ dualL X from ht) (a • x) hax
    refine ⟨o, ?_, ?_⟩
    · intro c hc
      obtain ⟨o', ho'⟩ := (show t ∈ dualL X from ht) (c • x) hc
      have : c * o = o' * a := by
        apply hinj
        show algebraMap (𝓞 K) K (c * o) = algebraMap (𝓞 K) K (o' * a)
        rw [map_mul, map_mul, ho, ho', smul_dot, smul_dot]
        ring
      rw [this, Ideal.mem_span_singleton']
      exact ⟨o', rfl⟩
    · show algebraMap (𝓞 K) K o = algebraMap (𝓞 K) K a * (x ⬝ᵥ t)
      rw [ho, smul_dot]
  have hmapQ : ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((qI (aI X x) a).toAddSubgroup.map mO) =
      (Ideal.span {a}).toAddSubgroup.relIndex (qI (aI X x) a).toAddSubgroup :=
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hrel : (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup =
      ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((dualL X).toAddSubgroup.map ψ) := by
    rw [claim1, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap]
  have hQne : ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((qI (aI X x) a).toAddSubgroup.map mO) ≠ 0 := by
    rw [hmapQ]; exact hq0
  rw [hrel]
  refine ⟨fun h => hQne (AddSubgroup.relIndex_eq_zero_of_le_right claim2 h), ?_⟩
  calc ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((dualL X).toAddSubgroup.map ψ)
      ≤ ((Ideal.span {a}).toAddSubgroup.map mO).relIndex ((qI (aI X x) a).toAddSubgroup.map mO) :=
        AddSubgroup.relIndex_le_of_le_right claim2 hQne
    _ = (Ideal.span {a}).toAddSubgroup.relIndex (qI (aI X x) a).toAddSubgroup := hmapQ
    _ ≤ Ideal.absNorm (aI X x) := hqle
    _ ≤ _ := hNle
end PI.UnitaryGroupMassFormula.LCG.DIdx
