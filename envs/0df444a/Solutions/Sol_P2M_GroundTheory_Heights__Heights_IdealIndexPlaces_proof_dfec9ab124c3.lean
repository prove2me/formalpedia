-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_proof_dfec9ab124c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:48:10.649697+00:00
-- url     : https://prove2.me/submissions/8feccf7e-cd56-4a54-ac2d-158435b084fe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsPointHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FieldChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIdealIndexPlaces
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_genIndex_comap_718e6a574b11
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IdealIndexPlaces_genIndex_ideal_8d3b6b12661a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasFiniteMulSupport_iSup_place_6bf3c48ba8b2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open IdealIndexPlaces
namespace GroundTheory.Heights₂.Heights
namespace IdealIndexPlaces
theorem _root_.solution : IdealIndexPlaces.Statement := by
  intro L _ _ ι _ y hy
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 L)) y
  choose z hz using hint
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbL : (b : L) ≠ 0 := by rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  have hzy : ∀ i, ((z i : 𝓞 L) : L) = (b : L) * y i := fun i ↦ by
    have h := hz i
    simp only [Algebra.smul_def] at h
    exact h
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  replace hi0 : y i0 ≠ 0 := hi0
  set c : 𝓞 L := z i0 with hc
  have hcy : (c : L) = b * y i0 := hzy i0
  have hcL : (c : L) ≠ 0 := by rw [hcy]; exact mul_ne_zero hbL hi0
  have hc0 : c ≠ 0 := fun h ↦ hcL (by rw [h]; rfl)
  set M := multiplierIdeal y with hMdef
  let g : 𝓞 L →ₗ[𝓞 L] L :=
    (LinearMap.mulLeft (𝓞 L) ((c : L)⁻¹)).comp (Algebra.linearMap (𝓞 L) L)
  have hg : ∀ t, g t = (c : L)⁻¹ * t := fun t ↦ rfl
  set I : Ideal (𝓞 L) := M.comap g with hIdef
  set J : Ideal (𝓞 L) := Ideal.span (Set.range z) with hJdef
  have hI : ∀ t : 𝓞 L, t ∈ I ↔ ∀ i, t * z i ∈ Ideal.span {c * b} := by
    intro t
    change (∀ i, (c : L)⁻¹ * t * y i ∈ Set.range (algebraMap (𝓞 L) L)) ↔ _
    refine forall_congr' fun i ↦ ?_
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨e, he⟩
      refine ⟨e, RingOfIntegers.ext ?_⟩
      change (e : L) * ((c : L) * b) = t * z i
      change (e : L) = _ at he
      rw [he, hzy i]
      field_simp
    · rintro ⟨e, he⟩
      refine ⟨e, ?_⟩
      have he' : (e : L) * ((c : L) * b) = t * z i := congrArg (fun s : 𝓞 L ↦ (s : L)) he
      rw [hzy i] at he'
      have h3 : (e : L) * c = t * y i := mul_right_cancel₀ hbL (by linear_combination he')
      change (e : L) = _
      field_simp
      linear_combination h3

  have hIJ : I * J ≤ Ideal.span {c * b} := by
    refine Ideal.mul_le.mpr fun t ht s hs ↦ ?_
    have hle : J ≤ Submodule.comap (LinearMap.mulLeft (𝓞 L) t) (Ideal.span {c * b}) :=
      Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact (hI t).mp ht i)
    exact hle hs
  have hcbJ : Ideal.span {c * b} ≤ J :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mul_mem_right b J (Ideal.subset_span ⟨i0, rfl⟩))
  have hcb0 : Ideal.span {c * b} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact mul_ne_zero hc0 hb0
  have hJ0 : J ≠ ⊥ := fun h ↦ hcb0 (le_bot_iff.mp (h ▸ hcbJ))
  obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.mpr hcbJ
  have hKI : K ≤ I := fun t ht ↦ (hI t).mpr fun i ↦ by
    rw [hK, mul_comm t]; exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_range_self i)) ht
  have hIK : I ≤ K := by
    have h : J * K ∣ J * I := Ideal.dvd_iff_le.mpr (by rw [mul_comm J I, ← hK]; exact hIJ)
    exact Ideal.le_of_dvd ((mul_dvd_mul_iff_left hJ0).mp h)
  have hIeq : I = K := le_antisymm hIK hKI
  have hI0 : I ≠ ⊥ := by
    intro h; rw [hIeq] at h; rw [h, Ideal.mul_bot] at hK; exact hcb0 hK
  have hnorm : (I.absNorm : ℝ) * J.absNorm =
      |((Algebra.norm ℤ c : ℤ) : ℝ)| * |((Algebra.norm ℤ b : ℤ) : ℝ)| := by
    have h := congrArg (fun A ↦ (Ideal.absNorm A : ℝ)) hK
    simp only [map_mul, Ideal.absNorm_span_singleton, Int.natAbs_mul, Nat.cast_mul,
      Nat.cast_natAbs] at h
    rw [hIeq]
    push_cast at h
    linear_combination -1 * h

  set C : Ideal (𝓞 L) := (1 : Submodule (𝓞 L) L).comap g with hCdef
  have hC : C = Ideal.span {c} := by
    ext t
    rw [Ideal.mem_span_singleton']
    show g t ∈ (1 : Submodule (𝓞 L) L) ↔ _
    rw [Submodule.mem_one, hg]
    constructor
    · rintro ⟨e, he⟩
      refine ⟨e, RingOfIntegers.ext ?_⟩
      change (e : L) * c = t
      change (e : L) = _ at he
      rw [he]
      field_simp
    · rintro ⟨e, rfl⟩
      refine ⟨e, ?_⟩
      change (e : L) = (c : L)⁻¹ * ((e : L) * c)
      field_simp
  have hrange1 : M.toAddSubgroup ≤ g.toAddMonoidHom.range := by
    intro a ha
    have ha' : a ∈ M := ha
    obtain ⟨e, he⟩ := ha' i0
    refine ⟨b * e, ?_⟩
    change (c : L)⁻¹ * ((b : L) * e) = a
    change (e : L) = _ at he
    rw [he, hcy]
    field_simp
  have hrange2 : (1 : Submodule (𝓞 L) L).toAddSubgroup ≤ g.toAddMonoidHom.range := by
    intro a ha
    obtain ⟨e, rfl⟩ := Submodule.mem_one.mp ha
    refine ⟨c * e, ?_⟩
    change (c : L)⁻¹ * ((c : L) * e) = e
    field_simp
  have hC0 : C ≠ ⊥ := by rw [hC, Ne, Ideal.span_singleton_eq_bot]; exact hc0
  have hgen : genIndex M.toAddSubgroup (1 : Submodule (𝓞 L) L).toAddSubgroup =
      |((Algebra.norm ℤ c : ℤ) : ℝ)| / I.absNorm := by
    rw [← genIndex_comap g.toAddMonoidHom hrange1 hrange2]
    have e1 : M.toAddSubgroup.comap g.toAddMonoidHom = I.toAddSubgroup := rfl
    have e2 : (1 : Submodule (𝓞 L) L).toAddSubgroup.comap g.toAddMonoidHom = C.toAddSubgroup := rfl
    rw [e1, e2, genIndex_ideal hI0 hC0, hC, Ideal.absNorm_span_singleton, Nat.cast_natAbs]
    push_cast
    rfl

  have hz0 : z ≠ 0 := fun h ↦ hc0 (congrFun h i0)
  have hprodz := absNorm_mul_finprod_finitePlace_eq_one hz0
  have hsup : ∀ w : FinitePlace L, ⨆ i, w (z i : L) = w (b : L) * ⨆ i, w (y i) := by
    intro w
    simp_rw [hzy, map_mul]
    exact (Real.mul_iSup_of_nonneg (apply_nonneg w _) _).symm
  simp_rw [hsup] at hprodz
  rw [finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hbL) (hasFiniteMulSupport_iSup_place hy),
    FinitePlace.prod_eq_inv_abs_norm_int hb0] at hprodz
  rw [hgen]
  set P := ∏ᶠ w : FinitePlace L, ⨆ i, w (y i) with hPdef
  have hbn : |((Algebra.norm ℤ b : ℤ) : ℝ)| ≠ 0 := by
    rw [abs_ne_zero, Int.cast_ne_zero, Ne, Algebra.norm_eq_zero_iff]; exact hb0
  have hIn : (I.absNorm : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
  have hJn : (J.absNorm : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ0)
  have hinv := mul_inv_cancel₀ hbn
  have hP : (J.absNorm : ℝ) * P = |((Algebra.norm ℤ b : ℤ) : ℝ)| := by
    linear_combination |((Algebra.norm ℤ b : ℤ) : ℝ)| * hprodz - (J.absNorm : ℝ) * P * hinv
  rw [div_mul_eq_mul_div, div_eq_one_iff_eq hIn]
  apply mul_left_cancel₀ hJn
  linear_combination |((Algebra.norm ℤ c : ℤ) : ℝ)| * hP - hnorm
end IdealIndexPlaces
end GroundTheory.Heights₂.Heights
