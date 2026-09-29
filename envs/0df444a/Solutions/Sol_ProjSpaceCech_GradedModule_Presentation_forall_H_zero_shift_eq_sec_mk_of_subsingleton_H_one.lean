-- Prove2me | solution 1 for ProjSpaceCech.GradedModule.Presentation.forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/68c58a66-d919-53fa-b360-90952638bfa8

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule

import Theorems.Thm_ProjSpaceCech_GradedModule_d_sq
import Theorems.Thm_ProjSpaceCech_GradedModule_Hom_secMap_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one

set_option autoImplicit false

universe u

namespace SESBody

open ProjSpaceCech ProjSpaceCech.GradedModule

variable {R : Type u} [CommRing R] {n : ℕ}

theorem secMap_mk {D₁ D₂ : GradedModule R n} (φ : GradedModule.Hom D₁ D₂) (I : Finset (Fin (n + 1))) (x : GradedModule.Frac D₁ I) :
    GradedModule.Hom.secMap φ I (GradedModule.sec.mk D₁ I x) =
      GradedModule.sec.mk D₂ I ⟨x.denExp, x.hden, φ.toLinearMap x.num, φ.mem_grade _ _ x.hnum⟩ := rfl

theorem cochainMap_apply {D₁ D₂ : GradedModule R n} (φ : GradedModule.Hom D₁ D₂) (i : ℕ) (f : GradedModule.cochain D₁ i) (s : Idx n i) :
    GradedModule.Hom.cochainMap φ i f s = GradedModule.Hom.secMap φ (Idx.img n s) (f s) := rfl

variable {D : GradedModule R n} (σ : GradedModule.Presentation D) (d : ℤ)

theorem secMap_shift_surjective (I : Finset (Fin (n + 1)))
    (x : GradedModule.sec (GradedModule.shift D d) I) :
    ∃ y : GradedModule.sec (GradedModule.shift σ.F d) I, GradedModule.Hom.secMap (σ.hom.shift d) I y = x := by
  induction x using Quotient.inductionOn with
  | h x =>
    obtain ⟨a, ha, m, hm⟩ := x
    obtain ⟨m', hm', rfl⟩ := σ.surj _ m hm
    exact ⟨GradedModule.sec.mk _ I ⟨a, ha, m', hm'⟩, rfl⟩

theorem exists_secMap_kerIncl_eq_of_secMap_eq_zero (I : Finset (Fin (n + 1)))
    (y : GradedModule.sec (GradedModule.shift σ.F d) I) (hy : GradedModule.Hom.secMap (σ.hom.shift d) I y = 0) :
    ∃ z : GradedModule.sec (GradedModule.shift σ.ker d) I, GradedModule.Hom.secMap (σ.kerIncl.shift d) I z = y := by
  induction y using Quotient.inductionOn with
  | h y =>
    obtain ⟨a, ha, m, hm⟩ := y

    have hy2 : GradedModule.sec.mk (GradedModule.shift D d) I ⟨a, ha, σ.hom.toLinearMap m, (σ.hom.shift d).mem_grade _ _ hm⟩ =
        GradedModule.sec.mk (GradedModule.shift D d) I ⟨0, fun _ _ => rfl, 0, by simp⟩ := hy
    obtain ⟨c, hc, hrel⟩ := (GradedModule.sec_mk_eq (GradedModule.shift D d) I).1 hy2
    have hzero : σ.hom.toLinearMap (GradedModule.monMul σ.F (c + 0) m) = 0 := by
      rw [GradedModule.Hom.map_monMul]
      have : GradedModule.monMul (GradedModule.shift D d) (c + 0) (σ.hom.toLinearMap m) =
          GradedModule.monMul (GradedModule.shift D d) (c + a) 0 := hrel
      rw [map_zero] at this
      exact this

    have hgr : GradedModule.monMul σ.F (c + 0) m ∈ σ.F.grade ((∑ j, ((a + (c + 0)) j : ℤ)) + d) := by
      have h1 := GradedModule.monMul_mem_grade σ.F (c + 0) _ m hm
      have : (∑ j, (a j : ℤ)) + d + ∑ j, ((c + 0) j : ℤ) = (∑ j, ((a + (c + 0)) j : ℤ)) + d := by
        simp only [Pi.add_apply, Pi.zero_apply, add_zero, Nat.cast_add, Finset.sum_add_distrib]; ring
      rw [← this]; exact h1
    refine ⟨GradedModule.sec.mk _ I ⟨a + (c + 0), GradedModule.Frac.supp_add I ha (GradedModule.Frac.supp_add I hc (fun _ _ => rfl)),
      GradedModule.monMul σ.F (c + 0) m, ⟨hgr, hzero⟩⟩, ?_⟩
    rw [secMap_mk]
    refine (GradedModule.sec_mk_eq _ I).2 ⟨0, fun _ _ => rfl, ?_⟩
    show GradedModule.monMul σ.F (0 + a) (GradedModule.monMul σ.F (c + 0) m) = GradedModule.monMul σ.F (0 + (a + (c + 0))) m
    rw [← GradedModule.monMul_add_apply]
    exact GradedModule.monMul_congr σ.F (fun j => by simp only [Pi.add_apply, Pi.zero_apply]; omega) m

theorem secMap_secMap_kerIncl (I : Finset (Fin (n + 1))) (z : GradedModule.sec (GradedModule.shift σ.ker d) I) :
    GradedModule.Hom.secMap (σ.hom.shift d) I (GradedModule.Hom.secMap (σ.kerIncl.shift d) I z) = 0 := by
  induction z using Quotient.inductionOn with
  | h z =>
    obtain ⟨a, ha, k, hk⟩ := z
    show GradedModule.Hom.secMap (σ.hom.shift d) I (GradedModule.Hom.secMap (σ.kerIncl.shift d) I (GradedModule.sec.mk _ I ⟨a, ha, k, hk⟩)) = 0
    rw [secMap_mk, secMap_mk]
    refine (GradedModule.sec_mk_eq _ I).2 ⟨0, fun _ _ => rfl, ?_⟩
    have h0 : σ.hom.toLinearMap k = 0 := hk.2
    show GradedModule.monMul (GradedModule.shift D d) (0 + 0) (σ.hom.toLinearMap (σ.kerIncl.toLinearMap k)) =
      GradedModule.monMul (GradedModule.shift D d) (0 + a) 0
    have h0' : σ.hom.toLinearMap (σ.kerIncl.toLinearMap k) = 0 := h0
    rw [h0']
    exact (LinearMap.map_zero _).trans (LinearMap.map_zero _).symm

end SESBody

open SESBody ProjSpaceCech ProjSpaceCech.GradedModule in
theorem solution
    {R : Type u} [CommRing R] {n : ℕ} {D : ProjSpaceCech.GradedModule R n}
    (σ : ProjSpaceCech.GradedModule.Presentation D) (d : ℤ)
    (hK : Subsingleton (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift σ.ker d) 1))
    (hF : ∀ c : ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift σ.F d) 0,
      ∃ f : σ.F.M, f ∈ σ.F.grade d ∧
        ∃ hf : f ∈ (ProjSpaceCech.GradedModule.shift σ.F d).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)),
          ∀ s : ProjSpaceCech.Idx n 0,
            (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (ProjSpaceCech.GradedModule.shift σ.F d) 0)) from c).1 s =
              ProjSpaceCech.GradedModule.sec.mk (ProjSpaceCech.GradedModule.shift σ.F d) (ProjSpaceCech.Idx.img n s)
                ⟨0, fun _ _ => rfl, f, hf⟩) :
    ∀ c : ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift D d) 0,
      ∃ m : D.M, m ∈ D.grade d ∧
        ∃ hm : m ∈ (ProjSpaceCech.GradedModule.shift D d).grade (∑ j : Fin (n + 1), (((0 : Fin (n + 1) → ℕ) j : ℕ) : ℤ)),
          ∀ s : ProjSpaceCech.Idx n 0,
            (show ↥(LinearMap.ker (ProjSpaceCech.GradedModule.d (ProjSpaceCech.GradedModule.shift D d) 0)) from c).1 s =
              ProjSpaceCech.GradedModule.sec.mk (ProjSpaceCech.GradedModule.shift D d) (ProjSpaceCech.Idx.img n s)
                ⟨0, fun _ _ => rfl, m, hm⟩ := by
  classical
  intro c
  have hc0 : GradedModule.d (GradedModule.shift D d) 0 (show ↥(LinearMap.ker (GradedModule.d (GradedModule.shift D d) 0)) from c).1 = 0 := (show ↥(LinearMap.ker (GradedModule.d (GradedModule.shift D d) 0)) from c).2

  choose fl hfl using fun s : Idx n 0 => secMap_shift_surjective σ d (Idx.img n s) ((show ↥(LinearMap.ker (GradedModule.d (GradedModule.shift D d) 0)) from c).1 s)
  let f : GradedModule.cochain (GradedModule.shift σ.F d) 0 := fl
  have hf : GradedModule.Hom.cochainMap (σ.hom.shift d) 0 f = (show ↥(LinearMap.ker (GradedModule.d (GradedModule.shift D d) 0)) from c).1 := funext fun s => hfl s

  have hgπ : GradedModule.Hom.cochainMap (σ.hom.shift d) 1 (GradedModule.d (GradedModule.shift σ.F d) 0 f) = 0 := by
    rw [← LinearMap.comp_apply, ← GradedModule.Hom.cochainMap_comm, LinearMap.comp_apply, hf, hc0]
  choose hl hhl using fun t : Idx n 1 =>
    exists_secMap_kerIncl_eq_of_secMap_eq_zero σ d (Idx.img n t) (GradedModule.d (GradedModule.shift σ.F d) 0 f t) (congrFun hgπ t)
  let h : GradedModule.cochain (GradedModule.shift σ.ker d) 1 := hl
  have hh : GradedModule.Hom.cochainMap (σ.kerIncl.shift d) 1 h = GradedModule.d (GradedModule.shift σ.F d) 0 f := funext fun t => hhl t

  have hinjι : Function.Injective (σ.kerIncl.shift d).toLinearMap := fun x y hxy => hxy
  have hker : GradedModule.d (GradedModule.shift σ.ker d) 1 h = 0 := by
    have hinj2 : Function.Injective (GradedModule.Hom.cochainMap (σ.kerIncl.shift d) 2) := by
      intro x y hxy
      funext s
      exact GradedModule.Hom.secMap_injective (σ.kerIncl.shift d) hinjι (Idx.img n s) (congrFun hxy s)
    apply hinj2
    rw [map_zero, ← LinearMap.comp_apply, ← GradedModule.Hom.cochainMap_comm, LinearMap.comp_apply, hh,
      ← LinearMap.comp_apply, GradedModule.d_sq, LinearMap.zero_apply]

  have htop : (LinearMap.range (GradedModule.d (GradedModule.shift σ.ker d) 0)).comap (LinearMap.ker (GradedModule.d (GradedModule.shift σ.ker d) 1)).subtype = ⊤ :=
    Submodule.Quotient.subsingleton_iff.1 hK
  have hrange : h ∈ LinearMap.range (GradedModule.d (GradedModule.shift σ.ker d) 0) := by
    have : (⟨h, LinearMap.mem_ker.2 hker⟩ : ↥(LinearMap.ker (GradedModule.d (GradedModule.shift σ.ker d) 1))) ∈
        (LinearMap.range (GradedModule.d (GradedModule.shift σ.ker d) 0)).comap (LinearMap.ker (GradedModule.d (GradedModule.shift σ.ker d) 1)).subtype := by
      rw [htop]; exact Submodule.mem_top
    exact this
  obtain ⟨h₀, hh₀⟩ := hrange

  have hf'0 : GradedModule.d (GradedModule.shift σ.F d) 0 (f - GradedModule.Hom.cochainMap (σ.kerIncl.shift d) 0 h₀) = 0 := by
    rw [map_sub, ← LinearMap.comp_apply (f := GradedModule.d (GradedModule.shift σ.F d) 0), GradedModule.Hom.cochainMap_comm,
      LinearMap.comp_apply, hh₀, hh, sub_self]
  obtain ⟨f₀, hf₀d, hf₀, hf'eq⟩ := hF ⟨f - GradedModule.Hom.cochainMap (σ.kerIncl.shift d) 0 h₀, LinearMap.mem_ker.2 hf'0⟩

  refine ⟨σ.hom.toLinearMap f₀, σ.hom.mem_grade d f₀ hf₀d, (σ.hom.shift d).mem_grade _ _ hf₀, fun s => ?_⟩
  have hfs : f s = (f - GradedModule.Hom.cochainMap (σ.kerIncl.shift d) 0 h₀) s +
      GradedModule.Hom.cochainMap (σ.kerIncl.shift d) 0 h₀ s := by
    rw [Pi.sub_apply, sub_add_cancel]
  have hf'eqs : (f - GradedModule.Hom.cochainMap (σ.kerIncl.shift d) 0 h₀) s =
      GradedModule.sec.mk (GradedModule.shift σ.F d) (Idx.img n s) ⟨0, fun _ _ => rfl, f₀, hf₀⟩ := hf'eq s
  rw [← hf, cochainMap_apply, hfs, map_add, cochainMap_apply, secMap_secMap_kerIncl σ d, add_zero, hf'eqs, secMap_mk]
  rfl

end S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one
end P2MW
export P2MW.S_ProjSpaceCech_GradedModule_Presentation_forall_H_zero_shift_eq_sec_mk_of_subsingleton_H_one (solution)
