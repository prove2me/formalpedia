-- Prove2me | solution 1 for PI.SelfDualLoc.W.bwdDir_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:23.664671+00:00
-- url     : https://prove2.me/submissions/7233cbb2-7bab-4ef0-b265-022672ef4d60

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_HformSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_OneTmulMemOloc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_SelfDualLocOfDirs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_Assembly
import Theorems.Thm_PI_SelfDualLoc_W_hform_incl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace PI.SelfDualLoc.W
open PI.SelfDualLoc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
private theorem hform_add_left_self_dual_local_basis {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin m) (Fin m) A) (x x' y : Fin m → A) :
    hform σ J (x + x') y = hform σ J x y + hform σ J x' y := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
private theorem hform_add_right_self_dual_local_basis {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin m) (Fin m) A) (x y y' : Fin m → A) :
    hform σ J x (y + y') = hform σ J x y + hform σ J x y' := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
private theorem hform_smul_left_self_dual_local_basis {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin m) (Fin m) A) (c : A) (x y : Fin m → A) :
    hform σ J (c • x) y = σ c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
private theorem hform_smul_right_self_dual_local_basis {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin m) (Fin m) A) (c : A) (x y : Fin m → A) :
    hform σ J x (c • y) = c * hform σ J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
private theorem hform_zero_left' {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin m) (Fin m) A) (y : Fin m → A) : hform σ J 0 y = 0 := by
  simp [hform]
private theorem hform_zero_right' {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin m) (Fin m) A) (x : Fin m → A) : hform σ J x 0 = 0 := by
  simp [hform]
private theorem hform_finset_sum_smul_left {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin m) (Fin m) A) {ι : Type*} (s : Finset ι) (c : ι → A) (x : ι → Fin m → A)
    (y : Fin m → A) :
    hform σ J (∑ i ∈ s, c i • x i) y = ∑ i ∈ s, σ (c i) * hform σ J (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hform_zero_left']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hform_add_left_self_dual_local_basis, hform_smul_left_self_dual_local_basis, ih]
private theorem hform_finset_sum_smul_right {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A)
    (J : Matrix (Fin m) (Fin m) A) {ι : Type*} (s : Finset ι) (c : ι → A) (x : Fin m → A)
    (y : ι → Fin m → A) :
    hform σ J x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, c i * hform σ J x (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hform_zero_right']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hform_add_right_self_dual_local_basis, hform_smul_right_self_dual_local_basis, ih]
end PI.SelfDualLoc.W
end
end

set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace PI.SelfDualLoc.W
theorem _root_.solution (hN : Nondeg) (hSp : SpanTop) (hL : LocBasis) (hD : DualBasis)
    (hU : UnitLoc) : BwdDir := by
  intro F E _ _ _ _ _ n σ J v Lb T hfin hLb hdual hT y hy

  have hT0 : T ≠ 0 := by
    rintro rfl
    exact hT (by simp)
  have hspan := hSp F E n σ J Lb T hfin hdual hT0
  obtain ⟨x, s, hs, hxL, hxs⟩ := hL F E n v Lb hfin hspan
  have hs0 : s ≠ 0 := fun h => hs (h ▸ zero_mem _)
  set sE : E := algebraMap F E (s : F) with hsE
  have hsE0 : sE ≠ 0 := by
    rw [hsE, ne_eq, map_eq_zero_iff _ (algebraMap F E).injective]
    exact fun h => hs0 (RingOfIntegers.coe_eq_zero_iff.mp h)
  have hσs : (σ : E →+* E) sE = sE := σ.commutes _

  have hσint : ∀ a : 𝓞 E, (σ : E →+* E) (a : E) ∈ intOE E := fun a =>
    ⟨⟨σ (a : E), by
      rw [mem_integralClosure_iff]
      exact (RingOfIntegers.isIntegral_coe a).map σ.toRingHom.toIntAlgHom⟩,
      RingOfIntegers.map_mk _ _⟩

  have hspanx : Submodule.span E (Set.range x) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro z hz
    obtain ⟨a, ha⟩ := hxs z hz
    have h1 : sE • z ∈ Submodule.span E (Set.range x) := by
      rw [ha]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h2 := Submodule.smul_mem _ sE⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hsE0, one_smul] at h2

  have hpair : ∀ z ∈ Lb, ∀ w : Fin n → E, ∃ a : Fin n → 𝓞 E,
      sE * hform (σ : E →+* E) J z w =
        ∑ i, (σ : E →+* E) ((a i : 𝓞 E) : E) * hform (σ : E →+* E) J (x i) w := by
    intro z hz w
    obtain ⟨a, ha⟩ := hxs z hz
    refine ⟨a, ?_⟩
    rw [← hσs, ← hform_smul_left_self_dual_local_basis, ha, hform_finset_sum_smul_left]
  have hnondx : ∀ w : Fin n → E, (∀ i, hform (σ : E →+* E) J (x i) w = 0) → w = 0 := by
    intro w hw
    refine hN F E n σ J Lb T hfin hdual hT0 w fun z hz => ?_
    obtain ⟨a, ha⟩ := hpair z hz w
    simp only [hw, mul_zero, Finset.sum_const_zero] at ha
    exact (mul_eq_zero.mp ha).resolve_left hsE0
  obtain ⟨yd, hyd, hydspan⟩ := hD F E n σ J x hspanx hnondx

  have hTs : ∀ j, (T : E) • (sE • yd j) ∈ Lb := by
    intro j
    refine hdual _ fun z hz => ?_
    obtain ⟨a, ha⟩ := hpair z hz (yd j)
    rw [hform_smul_right_self_dual_local_basis, ha]
    simp only [hyd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hσint (a j)

  set w : Fin n → Fin n → E ⊗[F] v.adicCompletion F :=
    fun j k => inclE (F := F) (v.adicCompletion F) (yd j k) with hw
  have hTsv : (T * s : 𝓞 F) ∉ v.asIdeal := fun h => (v.isPrime.mem_or_mem h).elim hT hs
  obtain ⟨u, hu, hu1⟩ := hU F E v (T * s) hTsv
  have hwmem : ∀ j, w j ∈ Lloc F E n v Lb := by
    intro j
    have hg : (fun k => inclE (F := F) (v.adicCompletion F) (((T : E) • (sE • yd j)) k)) ∈
        Lloc F E n v Lb := Submodule.subset_span ⟨_, hTs j, rfl⟩
    have h2 := Submodule.smul_mem (Lloc F E n v Lb) (⟨u, hu⟩ : Oloc F E v) hg
    convert h2 using 1
    funext k
    rw [Subring.smul_def, Pi.smul_apply, smul_eq_mul]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hw]
    have e : inclE (F := F) (v.adicCompletion F) (T : E) * inclE (F := F) (v.adicCompletion F) sE *
        u = 1 := by
      rw [← hu1]
      simp only [map_mul, map_natCast, hsE]
    linear_combination (-inclE (F := F) (v.adicCompletion F) (yd j k)) * e

  choose d hd using fun k => hydspan (Pi.single k 1)
  set c : Fin n → E ⊗[F] v.adicCompletion F :=
    fun j => ∑ k, y k * inclE (F := F) (v.adicCompletion F) (d k j) with hc
  have hyc : y = ∑ j, c j • w j := by
    funext l
    have hl : ∀ k, inclE (F := F) (v.adicCompletion F) ((Pi.single k (1 : E) : Fin n → E) l) =
        ∑ j, inclE (F := F) (v.adicCompletion F) (d k j) *
          inclE (F := F) (v.adicCompletion F) (yd j l) := by
      intro k
      conv_lhs => rw [hd k]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
    calc y l = ∑ k, y k * inclE (F := F) (v.adicCompletion F) ((Pi.single k (1 : E) : Fin n → E) l) := by
          simp [Pi.single_apply]
      _ = ∑ k, ∑ j, y k * inclE (F := F) (v.adicCompletion F) (d k j) *
            inclE (F := F) (v.adicCompletion F) (yd j l) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hl k, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = (∑ j, c j • w j) l := by
          rw [Finset.sum_comm]
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hc, hw, Finset.sum_mul]

  have hcint : ∀ i, c i ∈ Oloc F E v := by
    intro i
    have hxi : (fun k => inclE (F := F) (v.adicCompletion F) (x i k)) ∈ Lloc F E n v Lb :=
      Submodule.subset_span ⟨_, hxL i, rfl⟩
    have h := hy _ hxi
    unfold hloc at h
    rw [hyc, hform_finset_sum_smul_right] at h
    have h' : ∀ j, hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
        (fun k => inclE (F := F) (v.adicCompletion F) (x i k)) (w j) =
          if i = j then 1 else 0 := by
      intro j
      rw [hw]
      dsimp only
      rw [hform_incl, hyd]
      split_ifs <;> simp
    simp only [h', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
    exact h
  rw [hyc]
  exact Submodule.sum_mem _ fun j _ => by
    have := Submodule.smul_mem (Lloc F E n v Lb) (⟨c j, hcint j⟩ : Oloc F E v) (hwmem j)
    simpa [Subring.smul_def] using this
end PI.SelfDualLoc.W
