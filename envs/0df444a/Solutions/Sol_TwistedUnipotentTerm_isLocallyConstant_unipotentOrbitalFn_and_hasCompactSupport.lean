-- Prove2me | solution 1 for TwistedUnipotentTerm.isLocallyConstant_unipotentOrbitalFn_and_hasCompactSupport
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/88beff8e-59ef-5768-80e7-bc0f325dcdfb

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwistedUnipotentTerm_isLocallyConstant_unipotentOrbitalFn_and_hasCompactSupport

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter
open TensorProduct AutomorphicForm
open scoped TensorProduct.RightActions

noncomputable section

namespace TwistedUnipotentTermK6b

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev SL (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type :=
  L ⊗[K] v.adicCompletion K

abbrev Gsl (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) : Type :=
  GL (Fin 2) (SL K L v)

section Instances

scoped instance instIsTopologicalRingSL (v : HeightOneSpectrum (𝓞 K)) : IsTopologicalRing (SL K L v) :=
  isTopologicalRing_tensor K L _
scoped instance instT2SL (v : HeightOneSpectrum (𝓞 K)) : T2Space (SL K L v) := t2Space_tensor K L _
scoped instance instLocallyCompactSL (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (SL K L v) :=
  locallyCompactSpace_tensor K L _
scoped instance instFiniteExtension (v : HeightOneSpectrum (𝓞 K)) : Finite (v.Extension (𝓞 L)) :=
  HeightOneSpectrum.Extension.finite (𝓞 K) K L (𝓞 L) v
scoped instance instLocallyCompactGsl (v : HeightOneSpectrum (𝓞 K)) : LocallyCompactSpace (Gsl K L v) :=
  locallyCompactSpace_tensorGL K L _
scoped instance instIsTopologicalGroupGsl (v : HeightOneSpectrum (𝓞 K)) : IsTopologicalGroup (Gsl K L v) :=
  isTopologicalGroup_tensorGL K L _
scoped instance instT2Gsl (v : HeightOneSpectrum (𝓞 K)) : T2Space (Gsl K L v) := t2Space_tensorGL K L _
scoped instance instR1SL (v : HeightOneSpectrum (𝓞 K)) : R1Space (SL K L v) := T2Space.r1Space

end Instances

section IntegralSubgroup

variable {A : Type*} [CommRing A]

theorem mul_mem_integralUnitsSet (U : Subring A) {g h : GL (Fin 2) A}
    (hg : g ∈ integralUnitsSet (U : Set A)) (hh : h ∈ integralUnitsSet (U : Set A)) :
    g * h ∈ integralUnitsSet (U : Set A) := by
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    exact U.sum_mem fun k _ => U.mul_mem (hg.1 i k) (hh.1 k j)
  · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
    exact U.sum_mem fun k _ => U.mul_mem (hh.2 i k) (hg.2 k j)

end IntegralSubgroup

def semiLocalSubring (v : HeightOneSpectrum (𝓞 K)) : Subring (SL K L v) :=
  (HeightOneSpectrum.tensorAdicCompletionIntegersTo K L (𝓞 L) v).toRingHom.range

theorem coe_semiLocalSubring (v : HeightOneSpectrum (𝓞 K)) :
    (semiLocalSubring (K := K) (L := L) v : Set (SL K L v)) = semiLocalIntegers K L v := by
  ext x
  simp only [semiLocalSubring, RingHom.coe_range, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    semiLocalIntegers, Set.mem_range]

theorem mem_semiLocalSubring_iff (v : HeightOneSpectrum (𝓞 K)) (x : SL K L v) :
    x ∈ semiLocalSubring (K := K) (L := L) v ↔ x ∈ semiLocalIntegers K L v := by
  rw [← coe_semiLocalSubring]; rfl

theorem mul_mem_semiLocalIntegralSet (v : HeightOneSpectrum (𝓞 K)) {g h : Gsl K L v}
    (hg : g ∈ semiLocalIntegralSet K L v) (hh : h ∈ semiLocalIntegralSet K L v) :
    g * h ∈ semiLocalIntegralSet K L v := by
  have h' := mul_mem_integralUnitsSet (semiLocalSubring (K := K) (L := L) v)
    (by rw [coe_semiLocalSubring]; exact hg) (by rw [coe_semiLocalSubring]; exact hh)
  rwa [coe_semiLocalSubring] at h'

section Unipotent

variable (K L) (v : HeightOneSpectrum (𝓞 K))

theorem coe_semiLocalUnipotent (x : SL K L v) :
    ((TwistedUnipotentTerm.semiLocalUnipotent K L v x : Gsl K L v) : Matrix (Fin 2) (Fin 2) (SL K L v)) =
      !![1, x; 0, 1] := rfl

theorem coe_inv_semiLocalUnipotent (x : SL K L v) :
    (((TwistedUnipotentTerm.semiLocalUnipotent K L v x)⁻¹ : Gsl K L v) : Matrix (Fin 2) (Fin 2) (SL K L v)) =
      !![1, -x; 0, 1] := rfl

theorem semiLocalUnipotent_add (x u : SL K L v) :
    TwistedUnipotentTerm.semiLocalUnipotent K L v (x + u) =
      TwistedUnipotentTerm.semiLocalUnipotent K L v x * TwistedUnipotentTerm.semiLocalUnipotent K L v u := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_semiLocalUnipotent, coe_semiLocalUnipotent, coe_semiLocalUnipotent]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem semiLocalUnipotent_zero :
    TwistedUnipotentTerm.semiLocalUnipotent K L v 0 = 1 := by
  refine Units.ext ?_
  rw [coe_semiLocalUnipotent, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem semiLocalUnipotent_mem_semiLocalIntegralSet {u : SL K L v} (hu : u ∈ semiLocalIntegers K L v) :
    TwistedUnipotentTerm.semiLocalUnipotent K L v u ∈ semiLocalIntegralSet K L v := by
  have h0 := zero_mem_semiLocalIntegers K L v
  have h1 := one_mem_semiLocalIntegers K L v
  have hn : -u ∈ semiLocalIntegers K L v := by
    rw [← mem_semiLocalSubring_iff] at hu ⊢
    exact Subring.neg_mem _ hu
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [coe_semiLocalUnipotent]
    fin_cases i <;> fin_cases j <;> simp [h0, h1, hu]
  · rw [coe_inv_semiLocalUnipotent]
    fin_cases i <;> fin_cases j <;> simp [h0, h1, hn]

theorem mul_semiLocalUnipotent_mem_iff {u : SL K L v} (hu : u ∈ semiLocalIntegers K L v)
    (g : Gsl K L v) :
    g * TwistedUnipotentTerm.semiLocalUnipotent K L v u ∈ semiLocalIntegralSet K L v ↔
      g ∈ semiLocalIntegralSet K L v := by
  have hn : -u ∈ semiLocalIntegers K L v := by
    rw [← mem_semiLocalSubring_iff] at hu ⊢
    exact Subring.neg_mem _ hu
  constructor
  · intro h
    have h' := mul_mem_semiLocalIntegralSet v h (semiLocalUnipotent_mem_semiLocalIntegralSet K L v hn)
    rwa [mul_assoc, ← semiLocalUnipotent_add, add_neg_cancel, semiLocalUnipotent_zero, mul_one] at h'
  · intro h
    exact mul_mem_semiLocalIntegralSet v h (semiLocalUnipotent_mem_semiLocalIntegralSet K L v hu)

end Unipotent

section Invariance

variable (K L) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
  (w : v.Extension (𝓞 L)) (m : ℕ) (rT : Fin m → GL (Fin 2) (w.1.adicCompletion L))
  (z : GL (Fin 2) (w.1.adicCompletion L)) (k j : ℕ)

theorem wordIndicator_mul_semiLocalUnipotent {u : SL K L v} (hu : u ∈ semiLocalIntegers K L v)
    (g : Gsl K L v) :
    TwistedUnipotentTerm.wordIndicator K L v w m rT z k j (g * TwistedUnipotentTerm.semiLocalUnipotent K L v u) =
      TwistedUnipotentTerm.wordIndicator K L v w m rT z k j g := by
  unfold TwistedUnipotentTerm.wordIndicator
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [← mul_assoc]
  by_cases hg : (semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1
      ((List.ofFn fun i => rT (ι i)).prod * z ^ j)))⁻¹ * g ∈ semiLocalIntegralSet K L v
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((mul_semiLocalUnipotent_mem_iff K L v hu _).2 hg)]
  · rw [Set.indicator_of_notMem hg,
      Set.indicator_of_notMem (mt (mul_semiLocalUnipotent_mem_iff K L v hu _).1 hg)]

theorem unipotentOrbitalFn_add {u : SL K L v} (hu : u ∈ semiLocalIntegers K L v) (x : SL K L v) :
    TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w m rT z k j (x + u) =
      TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w m rT z k j x := by
  unfold TwistedUnipotentTerm.unipotentOrbitalFn
  simp only [semiLocalUnipotent_add, ← mul_assoc _ (TwistedUnipotentTerm.semiLocalUnipotent K L v x),
    wordIndicator_mul_semiLocalUnipotent K L v w m rT z k j hu]

theorem isLocallyConstant_unipotentOrbitalFn :
    IsLocallyConstant (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w m rT z k j) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hopen : IsOpen ((fun y : SL K L v => y - x) ⁻¹' semiLocalIntegers K L v) :=
    (isOpen_semiLocalIntegers K L v).preimage (continuous_id.sub continuous_const)
  have hmem : x ∈ (fun y : SL K L v => y - x) ⁻¹' semiLocalIntegers K L v := by
    simp only [Set.mem_preimage, sub_self]
    exact zero_mem_semiLocalIntegers K L v
  filter_upwards [hopen.mem_nhds hmem] with y hy
  have := unipotentOrbitalFn_add K L ξL v w m rT z k j hy x
  rwa [add_sub_cancel] at this

end Invariance

section Support

variable (K L) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K))
  (w : v.Extension (𝓞 L)) (m : ℕ) (rT : Fin m → GL (Fin 2) (w.1.adicCompletion L))
  (z : GL (Fin 2) (w.1.adicCompletion L)) (k j : ℕ)

def readOff (g : Gsl K L v) : SL K L v :=
  ((g⁻¹ : Gsl K L v) : Matrix (Fin 2) (Fin 2) (SL K L v)) 0 0 * (g : Matrix (Fin 2) (Fin 2) (SL K L v)) 0 1

theorem continuous_readOff : Continuous (readOff K L v) := by
  unfold readOff
  refine Continuous.mul ?_ ?_
  · exact (Units.continuous_coe_inv.matrix_elem 0 0)
  · exact (Units.continuous_val.matrix_elem 0 1)

theorem readOff_central_mul_unipotent (ζ : (SL K L v)ˣ) (x : SL K L v) :
    readOff K L v (TwistedUnipotentTerm.semiLocalCentral K L v ζ *
      TwistedUnipotentTerm.semiLocalUnipotent K L v x) = x := by
  unfold readOff
  rw [mul_inv_rev, Units.val_mul, Units.val_mul, coe_inv_semiLocalUnipotent, coe_semiLocalUnipotent]
  have h1 : ((TwistedUnipotentTerm.semiLocalCentral K L v ζ : Gsl K L v) : Matrix (Fin 2) (Fin 2) (SL K L v)) =
      Matrix.scalar (Fin 2) (ζ : SL K L v) := rfl
  have h2 : (((TwistedUnipotentTerm.semiLocalCentral K L v ζ)⁻¹ : Gsl K L v) :
      Matrix (Fin 2) (Fin 2) (SL K L v)) = Matrix.scalar (Fin 2) ((ζ⁻¹ : (SL K L v)ˣ) : SL K L v) := by
    unfold TwistedUnipotentTerm.semiLocalCentral
    rw [← map_inv]; rfl
  rw [h1, h2]
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, ← mul_assoc]

def wordSet : Set (Gsl K L v) :=
  ⋃ ι : Fin k → Fin m,
    (fun p : Gsl K L v × Gsl K L v => p.1 *
      (semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1
        ((List.ofFn fun i => rT (ι i)).prod * z ^ j)) * p.2)) ''
      (semiLocalIntegralSet K L v ×ˢ semiLocalIntegralSet K L v)

theorem isCompact_wordSet : IsCompact (wordSet K L v w m rT z k j) := by
  unfold wordSet
  refine isCompact_iUnion fun ι => ?_
  refine ((isCompact_semiLocalIntegralSet K L v).prod (isCompact_semiLocalIntegralSet K L v)).image ?_
  fun_prop

theorem mem_wordSet_of_wordIndicator_ne_zero {κ : Gsl K L v} (hκ : κ ∈ semiLocalIntegralSet K L v)
    {g : Gsl K L v} (h : TwistedUnipotentTerm.wordIndicator K L v w m rT z k j (κ⁻¹ * g) ≠ 0) :
    g ∈ wordSet K L v w m rT z k j := by
  unfold TwistedUnipotentTerm.wordIndicator at h
  obtain ⟨ι, -, hι⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Set.indicator_apply_ne_zero] at hι
  have hmem := hι.1
  set W := semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1
    ((List.ofFn fun i => rT (ι i)).prod * z ^ j)) with hW
  refine Set.mem_iUnion.2 ⟨ι, ?_⟩
  refine ⟨(κ, W⁻¹ * (κ⁻¹ * g)), ⟨hκ, hmem⟩, ?_⟩
  simp only [hW]
  group

def supportSet : Set (SL K L v) :=
  readOff K L v '' wordSet K L v w m rT z k j

theorem isCompact_supportSet : IsCompact (supportSet K L v w m rT z k j) :=
  (isCompact_wordSet K L v w m rT z k j).image (continuous_readOff K L v)

theorem wordIndicator_eq_zero_of_not_mem {x : SL K L v} (hx : x ∉ supportSet K L v w m rT z k j)
    (ζ : (SL K L v)ˣ) {κ : Gsl K L v} (hκ : κ ∈ semiLocalIntegralSet K L v) :
    TwistedUnipotentTerm.wordIndicator K L v w m rT z k j
      (κ⁻¹ * TwistedUnipotentTerm.semiLocalCentral K L v ζ * TwistedUnipotentTerm.semiLocalUnipotent K L v x) = 0 := by
  by_contra h
  rw [mul_assoc] at h
  have hg := mem_wordSet_of_wordIndicator_ne_zero K L v w m rT z k j hκ h
  exact hx ⟨_, hg, readOff_central_mul_unipotent K L v ζ x⟩

theorem integral_mul_setIntegral_eq_zero {α β : Type*} {_ : MeasurableSpace α} {_ : MeasurableSpace β}
    (μ : Measure α) (ν : Measure β) (s : Set β) (c : α → ℂ) (F : α → β → ℂ)
    (h : ∀ a, ∀ b ∈ s, F a b = 0) :
    ∫ a, c a * ∫ b in s, F a b ∂ν ∂μ = 0 := by
  have : (fun a => c a * ∫ b in s, F a b ∂ν) = fun _ => 0 := by
    funext a
    rw [setIntegral_eq_zero_of_forall_eq_zero (h a), mul_zero]
  rw [this, integral_zero]

theorem unipotentOrbitalFn_eq_zero_of_not_mem {x : SL K L v} (hx : x ∉ supportSet K L v w m rT z k j) :
    TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w m rT z k j x = 0 := by
  unfold TwistedUnipotentTerm.unipotentOrbitalFn
  exact integral_mul_setIntegral_eq_zero _ _ _ _ _
    fun ζ κ hκ => wordIndicator_eq_zero_of_not_mem K L v w m rT z k j hx ζ hκ

theorem hasCompactSupport_unipotentOrbitalFn :
    HasCompactSupport (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w m rT z k j) :=
  HasCompactSupport.intro (isCompact_supportSet K L v w m rT z k j)
    fun _ hx => unipotentOrbitalFn_eq_zero_of_not_mem K L ξL v w m rT z k j hx

end Support

end TwistedUnipotentTermK6b
p2m_reactivate "P2MW.S_TwistedUnipotentTerm_isLocallyConstant_unipotentOrbitalFn_and_hasCompactSupport.TwistedUnipotentTermK6b"

end
p2m_reactivate "P2MW.S_TwistedUnipotentTerm_isLocallyConstant_unipotentOrbitalFn_and_hasCompactSupport.TwistedUnipotentTermK6b"

open scoped TensorProduct TensorProduct.RightActions in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (m : ℕ) (rT : Fin m → GL (Fin 2) (w.1.adicCompletion L)) (z : GL (Fin 2) (w.1.adicCompletion L)) (k j : ℕ) :
    IsLocallyConstant (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w m rT z k j) ∧
      HasCompactSupport (TwistedUnipotentTerm.unipotentOrbitalFn K L ξL v w m rT z k j) :=
  ⟨TwistedUnipotentTermK6b.isLocallyConstant_unipotentOrbitalFn K L ξL v w m rT z k j,
    TwistedUnipotentTermK6b.hasCompactSupport_unipotentOrbitalFn K L ξL v w m rT z k j⟩

end S_TwistedUnipotentTerm_isLocallyConstant_unipotentOrbitalFn_and_hasCompactSupport
end P2MW
export P2MW.S_TwistedUnipotentTerm_isLocallyConstant_unipotentOrbitalFn_and_hasCompactSupport (solution)
