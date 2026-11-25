-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtension_proof_8d47388f535b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:15:08.555604+00:00
-- url     : https://prove2.me/submissions/b65107b1-ffc8-4028-b24a-f12936d84697

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PInvertibleIdealIndex
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_POrderIdealIndexExtension
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_index_ne_zero_of_zsmul_mem_ed4642d5576e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_exists_int_eq_mul_1252f130419c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrderIdealIndexExtensionAlt_exists_family_d92587ad9ad1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_map_mul_eq_span_e21061b2c6b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mem_one_of_mem_62c5ae2e4464
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_apply_3d722f96a277
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_injective_e116db2bcf37
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mul_mem_of_mem_156f7ffd60e1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_InvertibleIdealIndexAlt_mulBy_apply_3d722f96a277



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
noncomputable section
open OrderIdealIndexExtensionAlt InvertibleIdealIndexAlt
namespace GroundTheory.Heights₂.Heights
namespace OrderIdealIndexExtension
theorem _root_.solution : OrderIdealIndexExtension.Statement := by
  intro L _ _ B hB
  classical
  have := hB
  obtain ⟨S, hSfin, hS, N, hN, hNF⟩ := exists_family (L := L) (B := B)
  have : Fintype S := hSfin.fintype
  set v : S → L := fun x => ((x : 𝓞 L) : L) with hv
  set φ : (S → B) →ₗ[B] L := Fintype.linearCombination B v with hφ
  have hφinj : Function.Injective φ :=
    (linearIndependent_iff_injective_fintypeLinearCombination).mp hS
  set Fs := Submodule.span B ((fun x : 𝓞 L => (x : L)) '' S) with hFs
  have hrange : ∀ y, y ∈ Fs ↔ ∃ β, φ β = y := by
    intro y
    rw [← LinearMap.mem_range, hφ, Fintype.range_linearCombination, hFs, Set.image_eq_range]
  set O := (1 : Submodule (𝓞 L) L).toAddSubgroup with hO
  set F := Fs.toAddSubgroup with hF
  have hmemO : ∀ x : 𝓞 L, (x : L) ∈ O := fun x => Submodule.mem_one.mpr ⟨x, rfl⟩
  have hOmem : ∀ y ∈ O, ∃ x : 𝓞 L, (x : L) = y := fun y hy => Submodule.mem_one.mp hy
  have hBF : ∀ b : B, ∀ y ∈ F, (b : L) * y ∈ F := fun b y hy => by
    have h1 := Fs.smul_mem b hy
    rwa [Subring.smul_def, smul_eq_mul] at h1
  have hFO : F ≤ O := by
    intro y hy
    obtain ⟨β, rfl⟩ := (hrange y).1 hy
    rw [hφ, Fintype.linearCombination_apply]
    refine O.sum_mem fun j _ => ?_
    rw [Subring.smul_def, smul_eq_mul]
    exact mul_mem_of_mem (β j).2 (hmemO _)
  have hNO : ∀ y ∈ O, (N : L) * y ∈ F := by
    intro y hy
    obtain ⟨x, rfl⟩ := hOmem y hy
    exact hNF x

  let toO : 𝓞 L →+ O :=
    { toFun := fun x => ⟨(x : L), hmemO x⟩
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  have htoO : Function.Surjective toO := by
    intro y
    obtain ⟨x, hx⟩ := hOmem y y.2
    exact ⟨x, Subtype.ext hx⟩
  have : Module.Finite ℤ O := Module.Finite.of_surjective toO.toIntLinearMap htoO
  have hFOidx : F.relIndex O ≠ 0 := by
    refine index_ne_zero_of_zsmul_mem (F.addSubgroupOf O) hN fun x => ?_
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_zsmul, zsmul_eq_mul]
    exact hNO x x.2

  have hint : ∀ β, IsIntegral ℤ (φ β) := fun β => by
    obtain ⟨x, hx⟩ := hOmem _ (hFO ((hrange _).2 ⟨β, rfl⟩))
    rw [← hx]
    exact x.isIntegral_coe
  let g1 : (S → B) →+ 𝓞 L :=
    { toFun := fun β => ⟨φ β, hint β⟩
      map_zero' := RingOfIntegers.ext (by
        show φ 0 = algebraMap (𝓞 L) L 0
        rw [map_zero, map_zero])
      map_add' := fun x y => RingOfIntegers.ext (by
        show φ (x + y) = algebraMap (𝓞 L) L (_ + _)
        rw [map_add]
        exact (map_add (algebraMap (𝓞 L) L) (⟨φ x, hint x⟩ : 𝓞 L) ⟨φ y, hint y⟩).symm) }
  have hg1 : Function.Injective g1 := fun a b h => hφinj (congrArg (fun x : 𝓞 L => (x : L)) h)
  have hsurj : ∀ x : 𝓞 L, ∃ β, φ β = (N : L) * (x : L) := fun x => (hrange _).1 (hNF x)
  choose g2 hg2 using hsurj
  have hg2add : ∀ x y, g2 (x + y) = g2 x + g2 y := fun x y => hφinj (by
    rw [map_add, hg2, hg2, hg2]; push_cast; ring)
  let g2' : 𝓞 L →+ (S → B) := AddMonoidHom.mk' g2 hg2add
  have hg2inj : Function.Injective g2' := fun x y h => by
    have h1 := congrArg φ h
    simp only [g2', AddMonoidHom.mk'_apply, hg2] at h1
    exact RingOfIntegers.ext (mul_left_cancel₀ (Int.cast_ne_zero.mpr hN) h1)
  have hr1 := LinearMap.finrank_le_finrank_of_injective (f := g1.toIntLinearMap) hg1
  have hr2 := LinearMap.finrank_le_finrank_of_injective (f := g2'.toIntLinearMap) hg2inj
  have hrank : Module.finrank ℚ L = Fintype.card S * Module.finrank ℤ B := by
    rw [← RingOfIntegers.rank, le_antisymm hr2 hr1, Module.finrank_pi_fintype]
    simp
  refine ⟨Fintype.card S, (N : B), ?_, hrank, ?_, ?_⟩
  · intro h
    apply hN
    have h1 := congrArg (fun b : B => (b : L)) h
    simpa using h1
  · intro I hI
    obtain ⟨t, htI, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨c, hc, q, hcq⟩ := exists_int_eq_mul ht0
    refine index_ne_zero_of_zsmul_mem I.toAddSubgroup hc fun x => ?_
    rw [Submodule.mem_toAddSubgroup, zsmul_eq_mul, hcq, mul_assoc]
    exact I.mul_mem_right _ htI
  intro I hI hcase
  set J := (Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B))).toAddSubgroup with hJ
  set IF := (AddSubgroup.pi Set.univ (fun _ : S => I.toAddSubgroup)).map φ.toAddMonoidHom with hIF
  have hmemIF : ∀ y, y ∈ IF ↔ ∃ β : S → B, (∀ j, β j ∈ I) ∧ φ β = y := by
    intro y
    simp [hIF, AddSubgroup.mem_pi]
  have hFtop : (⊤ : AddSubgroup (S → B)).map φ.toAddMonoidHom = F := by
    ext y
    simp [hF, hrange]
  have hIFidx : IF.relIndex F = I.toAddSubgroup.index ^ Fintype.card S := by
    rw [← hFtop, hIF, AddSubgroup.relIndex_map_map_of_injective _ _ hφinj,
      AddSubgroup.relIndex_top_right, AddSubgroup.index_pi]
    simp
  have hJO : J ≤ O := by
    intro y hy
    refine (Submodule.span_le.mpr ?_) hy
    rintro _ ⟨b, -, rfl⟩
    exact mem_one_of_mem b.2
  have hIF_I : ∀ i ∈ I, ∀ y ∈ F, (i : L) * y ∈ IF := by
    intro i hi y hy
    obtain ⟨β, rfl⟩ := (hrange y).1 hy
    refine (hmemIF _).2 ⟨i • β, fun j => ?_, ?_⟩
    · simpa using I.mul_mem_right (β j) hi
    · rw [map_smul, Subring.smul_def, smul_eq_mul]
  have hB_IF : ∀ b : B, ∀ y ∈ IF, (b : L) * y ∈ IF := by
    intro b y hy
    obtain ⟨β, hβ, rfl⟩ := (hmemIF y).1 hy
    refine (hmemIF _).2 ⟨b • β, fun j => ?_, ?_⟩
    · simpa using I.mul_mem_left b (hβ j)
    · rw [map_smul, Subring.smul_def, smul_eq_mul]
  have hIF_F : IF ≤ F := by
    intro y hy
    obtain ⟨β, -, rfl⟩ := (hmemIF y).1 hy
    exact (hrange _).2 ⟨β, rfl⟩
  have hIF_J : IF ≤ J := by
    intro y hy
    obtain ⟨β, hβ, rfl⟩ := (hmemIF y).1 hy
    rw [hφ, Fintype.linearCombination_apply]
    refine J.sum_mem fun j _ => ?_
    have h1 : β j • v j = (j : 𝓞 L) • ((β j : B) : L) := by
      rw [Subring.smul_def, smul_eq_mul, Algebra.smul_def, mul_comm]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨β j, hβ j, rfl⟩)
  rcases hcase with hP | hcop
  ·
    obtain ⟨t, hIt⟩ : ∃ t : B, I = Ideal.span {t} :=
      ⟨_, (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
    have ht0 : (t : L) ≠ 0 := by
      intro h
      apply hI
      rw [hIt, Ideal.span_singleton_eq_bot]
      exact Subtype.ext h
    have hJt : J = O.map (mulBy (t : L)) := by
      rw [hJ, hIt, ← map_mul_eq_span t]
    have hIFt : IF = F.map (mulBy (t : L)) := by
      ext y
      rw [hmemIF]
      constructor
      · rintro ⟨β, hβ, rfl⟩
        have h1 : ∀ j, ∃ a : B, a * t = β j := fun j => by
          have := hβ j
          rw [hIt] at this
          exact Ideal.mem_span_singleton'.mp this
        choose a ha using h1
        refine ⟨φ a, (hrange _).2 ⟨a, rfl⟩, ?_⟩
        have h2 : β = t • a := funext fun j => by simp [← ha j, mul_comm]
        rw [h2, mulBy_apply, map_smul, Subring.smul_def, smul_eq_mul]
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨a, rfl⟩ := (hrange z).1 hz
        refine ⟨t • a, fun j => ?_, ?_⟩
        · rw [hIt]
          simpa using Ideal.mul_mem_right (a j) _ (Ideal.mem_span_singleton_self t)
        · rw [mulBy_apply, map_smul, Subring.smul_def, smul_eq_mul]
    have hFt : F.map (mulBy (t : L)) ≤ F := by
      rintro _ ⟨z, hz, rfl⟩
      exact hBF t z hz
    have hOt : O.map (mulBy (t : L)) ≤ O := by
      rintro _ ⟨z, hz, rfl⟩
      exact mul_mem_of_mem t.2 hz
    have e1 : (F.map (mulBy (t : L))).relIndex (O.map (mulBy (t : L))) = F.relIndex O :=
      AddSubgroup.relIndex_map_map_of_injective _ _ (mulBy_injective ht0)
    have h1 := (AddSubgroup.relIndex_mul_relIndex _ _ _ (AddSubgroup.map_mono hFO) hOt).trans
      (AddSubgroup.relIndex_mul_relIndex _ _ _ hFt hFO).symm
    rw [e1, mul_comm (AddSubgroup.relIndex _ F)] at h1
    have h2 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hFOidx) h1
    rw [hJt, h2, ← hIFt, hIFidx]
  ·
    have h1 : (1 : B) ∈ I ⊔ Ideal.span {(N : B)} := hcop ▸ Submodule.mem_top
    obtain ⟨i, hi, z, hz, hiz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    have hib : (i : L) + (b : L) * (N : L) = 1 := by
      have := congrArg (fun x : B => (x : L)) hiz
      simpa using this
    have key : ∀ y ∈ Submodule.span (𝓞 L) ((fun y : B => (y : L)) '' (I : Set B)), ∀ o : 𝓞 L,
        (N : L) * ((o : L) * y) ∈ IF := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨j, hj, rfl⟩ := hy
        intro o
        rw [show (N : L) * ((o : L) * (j : L)) = (j : L) * ((N : L) * (o : L)) by ring]
        exact hIF_I j hj _ (hNO _ (hmemO o))
      | zero =>
        intro o
        rw [mul_zero, mul_zero]
        exact IF.zero_mem
      | add y w _ _ hy hw =>
        intro o
        rw [mul_add, mul_add]
        exact IF.add_mem (hy o) (hw o)
      | smul a y _ hy =>
        intro o
        have h2 : (N : L) * ((o : L) * (a • y)) = (N : L) * (((o * a : 𝓞 L) : L) * y) := by
          rw [Algebra.smul_def]
          push_cast
          ring_nf
        rw [h2]
        exact hy (o * a)
    have hsup : J ⊔ F = O := by
      refine le_antisymm (sup_le hJO hFO) fun x hx => ?_
      obtain ⟨o, rfl⟩ := hOmem x hx
      have h2 : (o : L) = (i : L) * (o : L) + (b : L) * ((N : L) * (o : L)) := by
        linear_combination (-(o : L)) * hib
      rw [h2]
      refine AddSubgroup.add_mem_sup ?_ (hBF b _ (hNO _ hx))
      have h3 : (i : L) * (o : L) = o • (i : L) := by
        rw [Algebra.smul_def, mul_comm]
      rw [h3]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    have hinf : J ⊓ F = IF := by
      refine le_antisymm (fun y hy => ?_) (le_inf hIF_J hIF_F)
      have h2 : y = (i : L) * y + (b : L) * ((N : L) * y) := by
        linear_combination (-y) * hib
      rw [h2]
      refine IF.add_mem (hIF_I i hi y hy.2) (hB_IF b _ ?_)
      simpa using key y hy.1 1
    calc J.relIndex O = J.relIndex (J ⊔ F) := by rw [hsup]
      _ = J.relIndex F := AddSubgroup.relIndex_sup_left _ _
      _ = (J ⊓ F).relIndex F := (AddSubgroup.inf_relIndex_right _ _).symm
      _ = IF.relIndex F := by rw [hinf]
      _ = _ := hIFidx
end OrderIdealIndexExtension
end GroundTheory.Heights₂.Heights
