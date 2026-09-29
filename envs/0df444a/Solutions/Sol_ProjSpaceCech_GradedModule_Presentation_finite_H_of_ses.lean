-- Prove2me | solution 1 for ProjSpaceCech.GradedModule.Presentation.finite_H_of_ses
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/a7aa0985-76e4-5526-8fd9-4fddf79b2816

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Theorems.Thm_ProjSpaceCech_GradedModule_d_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

universe u

noncomputable section

open Finset Function MvPolynomial

namespace ProjSpaceCech
p2m_export "ProjSpaceCech" "Idx Idx.img GradedModule GradedModule.monMul GradedModule.monMul_add_apply GradedModule.monMul_mem_grade GradedModule.Frac GradedModule.Frac.supp_add GradedModule.sec GradedModule.sec.mk GradedModule.sec_mk_eq GradedModule.cochain GradedModule.d GradedModule.H GradedModule.Hom GradedModule.Hom.map_monMul GradedModule.Hom.secMap GradedModule.Hom.cochainMap GradedModule.Hom.cochainMap_comm GradedModule.Hom.cochainMapKer GradedModule.Hom.HMap GradedModule.Presentation GradedModule.Presentation.kerIncl GradedModule.d_sq"
p2m_open "ProjSpaceCech"

section SES

variable {R : Type u} [CommRing R] {n : ℕ} {D : GradedModule R n}
variable (σ : GradedModule.Presentation D)

local notation "ιC" => GradedModule.Hom.cochainMap (GradedModule.Presentation.kerIncl σ)
local notation "πC" => GradedModule.Hom.cochainMap σ.hom

namespace GradedModule p2m_export "ProjSpaceCech.GradedModule" "monMul monMul_add_apply monMul_mem_grade Frac Frac.supp_add sec sec.mk sec_mk_eq cochain d H Hom Hom.map_monMul Hom.secMap Hom.cochainMap Hom.cochainMap_comm Hom.cochainMapKer Hom.HMap Presentation Presentation.kerIncl mk grade d_sq" end GradedModule
p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.piC_surjective (i : ℕ) : Function.Surjective (πC i) := by
  intro f; classical
  have hk : ∀ s, ∃ g, GradedModule.Hom.secMap σ.hom (Idx.img n s) g = f s := by
    intro s; obtain ⟨x⟩ := f s
    obtain ⟨m', hm', hπ⟩ := σ.surj _ x.num x.hnum
    exact ⟨GradedModule.sec.mk _ _ ⟨x.denExp, x.hden, m', hm'⟩,
      (GradedModule.sec_mk_eq _ _).mpr ⟨0, fun _ _ => rfl, by simp [hπ]⟩⟩
  choose g hg using hk; exact ⟨g, funext hg⟩

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.iotaC_injective (i : ℕ) : Function.Injective (ιC i) := by
  have hinj : ∀ I, Function.Injective
      (GradedModule.Hom.secMap (GradedModule.Presentation.kerIncl σ) I) := by
    intro I z₁ z₂
    obtain ⟨x⟩ := z₁; obtain ⟨y⟩ := z₂
    intro h
    obtain ⟨c, hc, heq⟩ := (GradedModule.sec_mk_eq σ.F I).mp h
    exact (GradedModule.sec_mk_eq σ.ker I).mpr ⟨c, hc, heq⟩
  intro f g hfg; funext s
  exact hinj _ (congrFun hfg s)

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.altC_exact (i : ℕ) :
    LinearMap.ker (πC i) = LinearMap.range (ιC i) := by
  refine le_antisymm ?_ ?_
  · intro f hf; classical
    have hfs : ∀ s, ∃ g, GradedModule.Hom.secMap (GradedModule.Presentation.kerIncl σ) _ g = f s := by
      intro s
      obtain ⟨x, hx⟩ := Quotient.exists_rep (f s)
      have hfs0 : GradedModule.Hom.secMap σ.hom _ (f s) = 0 :=
        congrFun (LinearMap.mem_ker.mp hf) s
      rw [← hx] at hfs0
      obtain ⟨c, hc, heq⟩ := (GradedModule.sec_mk_eq D _).mp hfs0
      simp only [map_zero, add_zero] at heq
      have hK : GradedModule.monMul σ.F c x.num ∈ σ.K := by
        rw [LinearMap.mem_ker, GradedModule.Hom.map_monMul]; exact heq
      have hgr : GradedModule.monMul σ.F c x.num
          ∈ σ.F.grade (∑ j, ((c + x.denExp) j : ℤ)) := by
        have h := GradedModule.monMul_mem_grade σ.F c _ x.num x.hnum
        have hsum : (∑ j, (x.denExp j : ℤ)) + (∑ j, (c j : ℤ))
            = ∑ j, ((c + x.denExp) j : ℤ) := by
          simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]; ring
        rwa [hsum] at h
      refine ⟨GradedModule.sec.mk σ.ker _
        ⟨c + x.denExp, GradedModule.Frac.supp_add _ hc x.hden,
          GradedModule.monMul σ.F c x.num, ⟨hgr, hK⟩⟩, ?_⟩
      rw [← hx]
      refine (GradedModule.sec_mk_eq σ.F _).mpr ⟨0, fun _ _ => rfl, ?_⟩
      show GradedModule.monMul σ.F (0 + x.denExp) (GradedModule.monMul σ.F c x.num)
        = GradedModule.monMul σ.F (0 + (c + x.denExp)) x.num
      rw [zero_add, zero_add, ← GradedModule.monMul_add_apply, add_comm]
    choose g hg using hfs; exact ⟨g, funext hg⟩
  · rintro f ⟨g, rfl⟩
    refine LinearMap.mem_ker.mpr (funext fun s => ?_)
    obtain ⟨y, hy⟩ := Quotient.exists_rep (g s)
    show GradedModule.Hom.secMap σ.hom _
        (GradedModule.Hom.secMap (GradedModule.Presentation.kerIncl σ) _ (g s)) = 0
    rw [← hy]
    refine (GradedModule.sec_mk_eq D _).mpr ⟨0, fun _ _ => rfl, ?_⟩
    show GradedModule.monMul D 0 (σ.hom.toLinearMap y.num) = GradedModule.monMul D _ 0
    rw [LinearMap.mem_ker.mp y.hnum.2, map_zero, map_zero]

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.snake_data (i : ℕ)
    (z : ↥(LinearMap.ker (GradedModule.d D i))) :
    ∃ (k₀ : ↥(LinearMap.ker (GradedModule.d σ.ker (i + 1))))
      (f₀ : GradedModule.cochain σ.F i),
        πC i f₀ = z.1 ∧ ιC (i + 1) k₀.1 = GradedModule.d σ.F i f₀ ∧
        ∀ f, πC i f = z.1 → ∃ h, ιC (i + 1) k₀.1
          = GradedModule.d σ.F i f + ιC (i + 1) (GradedModule.d σ.ker i h) := by
  obtain ⟨f₀, hf₀⟩ := GradedModule.piC_surjective σ i z.1
  have hdF : GradedModule.d σ.F i f₀ ∈ LinearMap.range (ιC (i + 1)) := by
    rw [← GradedModule.altC_exact]
    refine LinearMap.mem_ker.mpr ?_
    rw [← LinearMap.comp_apply, ← GradedModule.Hom.cochainMap_comm, LinearMap.comp_apply, hf₀]
    exact LinearMap.mem_ker.mp z.2
  obtain ⟨k₀, hk₀⟩ := hdF
  have hk₀c : k₀ ∈ LinearMap.ker (GradedModule.d σ.ker (i + 1)) := by
    refine LinearMap.mem_ker.mpr (GradedModule.iotaC_injective σ (i + 2) ?_)
    rw [← LinearMap.comp_apply, ← GradedModule.Hom.cochainMap_comm, LinearMap.comp_apply, hk₀,
      map_zero]
    exact LinearMap.congr_fun (GradedModule.d_sq σ.F i) f₀
  refine ⟨⟨k₀, hk₀c⟩, f₀, hf₀, hk₀, fun f hf => ?_⟩
  have hdiff : f₀ - f ∈ LinearMap.range (ιC i) := by
    rw [← GradedModule.altC_exact]
    exact LinearMap.mem_ker.mpr (by rw [map_sub, hf₀, hf, sub_self])
  obtain ⟨h, hh⟩ := hdiff
  refine ⟨h, ?_⟩
  rw [← LinearMap.comp_apply, ← GradedModule.Hom.cochainMap_comm, LinearMap.comp_apply, hh,
    map_sub, hk₀]
  abel

p2m_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.delta0 (i : ℕ) :
    ↥(LinearMap.ker (GradedModule.d D i)) →ₗ[R] GradedModule.H σ.ker (i + 1) := by
  classical
  choose k₀ f₀ hf₀ hk₀ hany using GradedModule.snake_data σ i
  refine
    { toFun := fun z => Submodule.Quotient.mk (k₀ z)
      map_add' := fun z₁ z₂ => (Submodule.Quotient.eq _).mpr ?_
      map_smul' := fun r z => (Submodule.Quotient.eq _).mpr ?_ }
  · obtain ⟨h, hh⟩ := hany (z₁ + z₂) (f₀ z₁ + f₀ z₂) (by rw [map_add, hf₀, hf₀]; rfl)
    refine ⟨h, GradedModule.iotaC_injective σ (i + 1) ?_⟩
    simp only [Submodule.coe_subtype, AddSubgroupClass.coe_sub, AddSubmonoid.coe_add,
      Submodule.coe_toAddSubmonoid, map_sub, map_add]
    rw [hh, hk₀, hk₀, map_add]; abel
  · obtain ⟨h, hh⟩ := hany (r • z) (r • f₀ z) (by rw [map_smul, hf₀]; rfl)
    refine ⟨h, GradedModule.iotaC_injective σ (i + 1) ?_⟩
    simp only [Submodule.coe_subtype, AddSubgroupClass.coe_sub, SetLike.val_smul,
      map_sub, map_smul, RingHom.id_apply]
    rw [hh, hk₀, map_smul]; abel

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.ker_delta0_le (i : ℕ) :
    LinearMap.ker (GradedModule.delta0 σ i)
      ≤ LinearMap.range (GradedModule.Hom.cochainMapKer σ.hom i) := by
  classical
  intro z hz

  simp only [GradedModule.delta0, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk] at hz

  obtain ⟨h', hh'⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  simp only [Submodule.coe_subtype] at hh'

  obtain ⟨f₀, hf₀, hk₀, _⟩ := Classical.choose_spec (GradedModule.snake_data σ i z)

  have hdF : GradedModule.d σ.F i (f₀ - ιC i h') = 0 := by
    have hchain := LinearMap.congr_fun
      (GradedModule.Hom.cochainMap_comm (GradedModule.Presentation.kerIncl σ) i) h'
    simp only [LinearMap.comp_apply] at hchain
    rw [map_sub, hchain, hh', hk₀, sub_self]

  refine ⟨⟨f₀ - ιC i h', LinearMap.mem_ker.mpr hdF⟩, Subtype.ext ?_⟩
  show πC i (f₀ - ιC i h') = z.1
  have hιker : πC i (ιC i h') = 0 :=
    LinearMap.mem_ker.mp (GradedModule.altC_exact σ i ▸ ⟨h', rfl⟩)
  rw [map_sub, hf₀, hιker, sub_zero]

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.delta0_vanish_on_bdry (j : ℕ)
    (z : ↥(LinearMap.ker (GradedModule.d D (j + 1))))
    (hz : z.1 ∈ LinearMap.range (GradedModule.d D j)) :
    GradedModule.delta0 σ (j + 1) z = 0 := by
  classical
  obtain ⟨w, hw⟩ := hz
  obtain ⟨w', hw'⟩ := GradedModule.piC_surjective σ j w

  have hπf : πC (j + 1) (GradedModule.d σ.F j w') = z.1 := by
    rw [← LinearMap.comp_apply, ← GradedModule.Hom.cochainMap_comm, LinearMap.comp_apply, hw', hw]
  obtain ⟨_, _, _, hany⟩ :=
    Classical.choose_spec (GradedModule.snake_data σ (j + 1) z)
  obtain ⟨h, hh⟩ := hany _ hπf
  simp only [GradedModule.delta0, LinearMap.coe_mk, AddHom.coe_mk]
  refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨h,
    GradedModule.iotaC_injective σ (j + 2) ?_⟩
  have hsq : (GradedModule.d σ.F (j + 1)) ((GradedModule.d σ.F j) w') = 0 := by
    have h0 := LinearMap.congr_fun (GradedModule.d_sq σ.F j) w'
    rwa [LinearMap.comp_apply, LinearMap.zero_apply] at h0
  simp only [Submodule.coe_subtype, hh, hsq, zero_add]

namespace GradedModule p2m_export "ProjSpaceCech.GradedModule" "monMul monMul_add_apply monMul_mem_grade Frac Frac.supp_add sec sec.mk sec_mk_eq cochain d H Hom Hom.map_monMul Hom.secMap Hom.cochainMap Hom.cochainMap_comm Hom.cochainMapKer Hom.HMap Presentation Presentation.kerIncl mk grade d_sq" namespace Presentation p2m_export "ProjSpaceCech.GradedModule.Presentation" "F K ker kerIncl surj mk hom" end GradedModule.Presentation
p2m_open_scoped "ProjSpaceCech.GradedModule ProjSpaceCech.GradedModule.Presentation" in

theorem GradedModule.Presentation.finite_H_of_ses' [IsNoetherianRing R] (i : ℕ)
    (hF : Module.Finite R (GradedModule.H σ.F i))
    (hK : Module.Finite R (GradedModule.H σ.ker (i + 1))) :
    Module.Finite R (GradedModule.H D i) := by
  classical

  have hrange_α : (LinearMap.range (GradedModule.Hom.HMap σ.hom i)).FG := by
    rw [LinearMap.range_eq_map]; exact (Module.finite_def.mp hF).map _
  haveI hNα : IsNoetherian R
      ↥(LinearMap.range (GradedModule.Hom.HMap σ.hom i)) :=
    isNoetherian_of_fg_of_noetherian _ hrange_α
  haveI hNK : IsNoetherian R (GradedModule.H σ.ker (i + 1)) := by
    haveI := hK; exact isNoetherian_of_isNoetherianRing_of_finite R _

  have hker_δ_le : ∀ (δ : GradedModule.H D i →ₗ[R] GradedModule.H σ.ker (i + 1))
      (_ : LinearMap.ker δ ≤ LinearMap.range (GradedModule.Hom.HMap σ.hom i)),
      Module.Finite R (GradedModule.H D i) := by
    intro δ hδ
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker δ ?_ ?_⟩
    · rw [Submodule.map_top]
      exact (IsNoetherian.noetherian _ : (LinearMap.range δ).FG)
    ·
      rw [top_inf_eq]
      have hcomap : ((LinearMap.ker δ).comap
          (LinearMap.range (GradedModule.Hom.HMap σ.hom i)).subtype).FG :=
        IsNoetherian.noetherian _
      have hmap := hcomap.map (LinearMap.range (GradedModule.Hom.HMap σ.hom i)).subtype
      rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hδ] at hmap
  rcases i with _ | j
  · exact hker_δ_le (GradedModule.delta0 σ 0) (GradedModule.ker_delta0_le σ 0)
  ·
    refine hker_δ_le
      (Submodule.liftQ _ (GradedModule.delta0 σ (j + 1))
        (fun z hz => GradedModule.delta0_vanish_on_bdry σ j z hz)) ?_
    intro z hz
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have hw0 : GradedModule.delta0 σ (j + 1) w = 0 := by
      simp [Submodule.liftQ_apply] at hz
      exact hz
    obtain ⟨f', hf'⟩ := GradedModule.ker_delta0_le σ (j + 1) (LinearMap.mem_ker.mpr hw0)
    exact ⟨Submodule.Quotient.mk f', congrArg Submodule.Quotient.mk hf'⟩

end SES

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) (i : ℕ)
    (hF : Module.Finite R (ProjSpaceCech.GradedModule.H σ.F i)) (hK : Module.Finite R (ProjSpaceCech.GradedModule.H σ.ker (i + 1))) :
    Module.Finite R (ProjSpaceCech.GradedModule.H D i) :=
  ProjSpaceCech.GradedModule.Presentation.finite_H_of_ses' σ i hF hK

end

end S_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses
end P2MW
export P2MW.S_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses (solution)
