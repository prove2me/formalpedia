-- Prove2me | solution 1 for PI.Dv.ProjBW.projB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:05:29.703659+00:00
-- url     : https://prove2.me/submissions/50165de6-354e-490a-9bc2-aa3f962626ad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MajorantVanishing_MajAtZeroRight
import Theorems.Thm_PI_Dv_ProjBW_inner_realize
import Theorems.Thm_PI_Dv_ProjBW_majAt_zero_right
import Theorems.Thm_PI_Dv_ProjBW_mem_zl
import Theorems.Thm_PI_Dv_ProjBW_mem_range_iff
import Theorems.Thm_PI_Dv_ProjBW_degL_eq
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_HN_HeightGram_inner_realize
import Theorems.Thm_Formalism_HN_htImage
import Theorems.Thm_Formalism_HN_muChar
import Theorems.Thm_Formalism_HN_plLat
import Theorems.Thm_Formalism_HN_satBasic
import Theorems.Thm_Formalism_HN_slopeIneq
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
open PI PI.Dv PI.Dv.ProjBW
open NumberField Formalism.HN
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.Dv.ProjBW
theorem _root_.solution : PI.Dv.ProjB := by
  intro K _ _ _ _ A e n hP
  obtain ⟨hG, hn, hee, hnL, hsa⟩ := hP
  obtain ⟨hX, hFG, hspan⟩ := hG

  set ρ := Formalism.HermitianLatticesTheory.realize A.b A.X with hρ
  set L0 := PI.Dv.cutE A e A.L with hL0def
  set I := PI.Dv.imgE A (1 - e) A.L with hIdef
  have hee' : ∀ y, e (e y) = e y := fun y => by rw [← Module.End.mul_apply, hee]
  have hr : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hrN : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn

  have hnoeth : IsNoetherian (𝓞 K) A.L := isNoetherian_of_fg_of_noetherian _ hFG
  have hL0le : L0 ≤ A.L := inf_le_left
  have hfg0 : L0.FG := by
    have h1 := (IsNoetherian.noetherian (L0.comap A.L.subtype)).map A.L.subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.2 hL0le] at h1
  have hfgI : I.FG := hFG.map _
  obtain ⟨hlatL, hrkL, -⟩ := plLat K A.V A.ι A.b A.X hX A.L hFG
  obtain ⟨hlat0, hrk0, -⟩ := plLat K A.V A.ι A.b A.X hX L0 hfg0
  obtain ⟨hlatI, hrkI, -⟩ := plLat K A.V A.ι A.b A.X hX I hfgI

  have hL0eq : L0 = A.L ⊓ (LinearMap.ker (1 - e)).restrictScalars (𝓞 K) := by
    ext x
    simp only [hL0def, PI.Dv.cutE, Submodule.mem_inf, Submodule.restrictScalars_mem, LinearMap.mem_ker,
      mem_range_iff e hee, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, h2.symm⟩
  have hsat0 : IsSat ρ A.L L0 := by
    rw [hL0eq]
    exact (htImage K A.V A.ι A.V A.ι A.b A.X A.b A.X hX hX (1 - e) A.L hFG).1

  have hrkKI : rkK I = PI.Dv.dimE A (1 - e) := by
    unfold rkK PI.Dv.dimE
    have hIset : (I : Set A.V) = ((1 - e : Module.End K A.V) : A.V → A.V) '' (A.L : Set A.V) := by
      rw [hIdef, PI.Dv.imgE, Submodule.map_coe, LinearMap.coe_restrictScalars]
    rw [hIset, Submodule.span_image, hspan, Submodule.map_top]

  set S : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) :=
    Submodule.span ℝ ((zl ρ L0 : Submodule ℤ _) : Set (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)))
    with hSdef
  have hA : ∀ x ∈ A.L, ρ (e x) ∈ S := by
    intro x hx
    have hm : ((n : 𝓞 K)) • e x ∈ L0 := by
      refine ⟨hnL x hx, ?_⟩
      show ((n : 𝓞 K)) • e x ∈ LinearMap.range e
      rw [mem_range_iff e hee, LinearMap.map_smul_of_tower, hee']
    have h1 : ρ (((n : 𝓞 K)) • e x) ∈ S := Submodule.subset_span ⟨_, hm, rfl⟩
    rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h1
    have h2 := S.smul_mem ((n : ℝ)⁻¹) h1
    rwa [smul_smul, inv_mul_cancel₀ hnR.ne', one_smul] at h2
  have hB : ∀ x : A.V, ρ ((1 - e) x) ∈ Sᗮ := by
    intro x
    have hle : S ≤ (ℝ ∙ ρ ((1 - e) x))ᗮ := by
      rw [hSdef, Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
      have hz' : e z = z := (mem_range_iff e hee z).1 hz.2
      rw [real_inner_comm, inner_realize]
      refine Finset.sum_eq_zero fun v _ => ?_
      rw [← hz', hsa, LinearMap.sub_apply, Module.End.one_apply, map_sub, hee', sub_self, majAt_zero_right]
      simp
    rw [Submodule.mem_orthogonal]
    intro u hu
    have := hle hu
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at this
    rwa [real_inner_comm]
  have hproj : ∀ x ∈ A.L, Sᗮ.starProjection (ρ x) = ρ ((1 - e) x) := by
    intro x hx
    have hsplit : ρ x = ρ (e x) + ρ ((1 - e) x) := by
      rw [← map_add]
      congr 1
      simp [LinearMap.sub_apply]
    rw [hsplit, map_add, (Submodule.starProjection_apply_eq_zero_iff _).2
      (Submodule.le_orthogonal_orthogonal S (hA x hx)), zero_add,
      Submodule.starProjection_eq_self_iff.2 (hB x)]
  have hq : Formalism.F.quot (zl ρ A.L) (zl ρ L0) = zl ρ I := by
    ext w
    simp only [Formalism.F.quot, Submodule.mem_map, mem_zl]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨(1 - e) x, ⟨x, hx, rfl⟩, ?_⟩
      exact (hproj x hx).symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨ρ x, ⟨x, hx, rfl⟩, hproj x hx⟩

  have hsatL := satBasic (𝓞 K) A.V (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) ρ A.L hlatL
  have hq3 := hsatL.2.2.2.2.2.2.2 L0 hsat0
  rw [hq] at hq3
  obtain ⟨hrkq, hrkle, hdegq⟩ := hq3
  have hdeg : deg ρ I = deg ρ A.L - deg ρ L0 := hdegq
  have hrkq' : rk ρ I = rk ρ A.L - rk ρ L0 := hrkq
  have hrkle' : rk ρ L0 ≤ rk ρ A.L := hrkle
  have hsumZ : rk ρ I + rk ρ L0 = rk ρ A.L := by omega
  have hsum : rkK I + rkK L0 = rkK A.L := by
    rw [hrkI, hrk0, hrkL, ← mul_add] at hsumZ
    exact Nat.eq_of_mul_eq_mul_left hrN hsumZ

  have hbound : deg ρ I ≤ (muMax ρ A.L + Real.log n) * ((Module.finrank ℚ K : ℝ) * (rkK I : ℝ)) := by
    by_cases hI : I = ⊥
    · have h0 : rk ρ I = 0 := (hsatL.2.2.2.1 I (by rw [hI]; exact bot_le)).2 hI
      rw [hrkI] at h0
      have h0' : rkK I = 0 := by
        rcases Nat.mul_eq_zero.1 h0 with h | h
        · omega
        · exact h
      have hd : deg ρ I = 0 := by rw [hI]; exact hsatL.2.2.2.2.1
      rw [hd, h0']
      simp
    · have hmem : ∀ x ∈ I, ((n : 𝓞 K) • (LinearMap.id : A.V →ₗ[𝓞 K] A.V)) x ∈ A.L := by
        rintro _ ⟨y, hy, rfl⟩
        simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.coe_restrictScalars,
          LinearMap.sub_apply, Module.End.one_apply, smul_sub]
        exact A.L.sub_mem (A.L.smul_mem _ hy) (hnL y hy)
      let φ : I →ₗ[𝓞 K] A.L := ((n : 𝓞 K) • (LinearMap.id : A.V →ₗ[𝓞 K] A.V)).restrict hmem
      have hφ : ∀ x : I, ((φ x : A.L) : A.V) = ((n : 𝓞 K)) • (x : A.V) := fun x => rfl
      have hnorm : ∀ x : I, ‖ρ ((φ x : A.L) : A.V)‖ ≤ (n : ℝ) * ‖ρ (x : A.V)‖ := by
        intro x
        refine le_of_eq ?_
        rw [hφ, Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast]
      have hinj : Function.Injective φ := by
        intro x y hxy
        have h1 := congrArg (fun z : A.L => (z : A.V)) hxy
        simp only [hφ] at h1
        rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul K,
          ← Nat.cast_smul_eq_nsmul K] at h1
        exact Subtype.ext ((smul_right_inj (Nat.cast_ne_zero.2 hn.ne')).1 h1)
      have hmu := (slopeIneq (𝓞 K) A.V A.V (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2))
        (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) ρ ρ I A.L hlatI hlatL φ (n : ℝ) hnR hnorm).2 hinj hI
      have hdI := ((muChar (𝓞 K) A.V (EuclideanSpace ℝ (InfinitePlace K × A.ι × Fin 2)) ρ I hlatI hI).1
        (muMax ρ I)).1 le_rfl I le_rfl
      have hrkIR : (rk ρ I : ℝ) = (Module.finrank ℚ K : ℝ) * (rkK I : ℝ) := by
        rw [hrkI]; push_cast; ring
      rw [hrkIR] at hdI
      have hpos : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) * (rkK I : ℝ) := by positivity
      exact hdI.trans (mul_le_mul_of_nonneg_right hmu hpos)

  unfold PI.Dv.DegreeKernelLowerBound
  rw [degL_eq A hX A.L hFG, degL_eq A hX L0 hfg0, ← hrkKI]
  have hsumR : (rkK A.L : ℝ) = (rkK I : ℝ) + (rkK L0 : ℝ) := by exact_mod_cast hsum.symm
  have key : 2 * deg ρ A.L / (Module.finrank ℚ K : ℝ) - 2 * deg ρ L0 / (Module.finrank ℚ K : ℝ) ≤
      2 * (rkK I : ℝ) * (muMax ρ A.L + Real.log n) := by
    rw [← sub_div, div_le_iff₀ hr]
    nlinarith [hbound, hdeg]
  unfold PI.Dv.muMaxL muMaxDef
  rw [hsumR]
  nlinarith [key]
end PI.Dv.ProjBW
