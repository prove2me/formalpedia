-- Prove2me | solution 1 for ProjSpaceCech.GradedModule.exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/bca0ba60-bd51-5d7c-8cc9-03a983bd031c

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Theorems.Thm_ProjSpaceCech_GradedModule_subsingleton_cohomology_shift_of_isFG
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated

set_option autoImplicit false

universe u

namespace P2mSatSerreB

open ProjSpaceCech Finset

variable {R : Type u} [CommRing R] {n : ℕ} {D M : GradedModule R n}

def Saturated (h : GradedModule.Hom D M) : Prop :=
  ∀ (e : ℤ) (f : M.M), f ∈ M.grade e → ∀ j : Fin (n + 1),
    ∃ (N : ℕ) (f' : D.M), f' ∈ D.grade (e + N) ∧ h.toLinearMap f' = (M.xMul j ^ N) f

theorem saturated_shift {h : GradedModule.Hom D M} (hs : Saturated h) (d : ℤ) : Saturated (h.shift d) := by
  intro e f hf j
  obtain ⟨N, f', hf', hh⟩ := hs (e + d) f hf j
  refine ⟨N, f', ?_, hh⟩
  show f' ∈ D.grade (e + N + d)
  rwa [show e + (N : ℤ) + d = e + d + N by ring]

theorem sum_add_single (a : Fin (n + 1) → ℕ) (l : Fin (n + 1)) (N : ℕ) :
    (∑ j, ((a + Pi.single (M := fun _ : Fin (n + 1) => ℕ) l N) j : ℤ)) = (∑ j, (a j : ℤ)) + N := by
  have h1 : ∀ j, (((a + Pi.single (M := fun _ : Fin (n + 1) => ℕ) l N) j : ℕ) : ℤ)
      = (a j : ℤ) + ((Pi.single (M := fun _ : Fin (n + 1) => ℕ) l N j : ℕ) : ℤ) := fun j => by
    rw [Pi.add_apply, Nat.cast_add]
  simp only [h1, sum_add_distrib, add_right_inj]
  rw [Finset.sum_eq_single l (fun j _ hj => by rw [Pi.single_eq_of_ne hj, Nat.cast_zero])
    (fun hl => absurd (mem_univ l) hl), Pi.single_eq_same]

theorem secMap_mk (h : GradedModule.Hom D M) (I : Finset (Fin (n + 1))) (x : GradedModule.Frac D I) :
    h.secMap I (GradedModule.sec.mk D I x)
      = GradedModule.sec.mk M I ⟨x.denExp, x.hden, h.toLinearMap x.num, h.mem_grade _ _ x.hnum⟩ := rfl

theorem secMap_surjective {h : GradedModule.Hom D M} (hs : Saturated h) (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
    Function.Surjective (h.secMap I) := by
  obtain ⟨l, hl⟩ := hI
  intro y
  induction y using Quotient.inductionOn with
  | h x =>
    obtain ⟨a, ha, m, hm⟩ := x
    obtain ⟨N, f', hf', hh⟩ := hs _ m hm l
    have ha' : ∀ j ∉ I, (a + Pi.single (M := fun _ : Fin (n + 1) => ℕ) l N) j = 0 := fun j hj => by
      have hjl : j ≠ l := fun e => hj (e ▸ hl)
      rw [Pi.add_apply, ha j hj, Pi.single_eq_of_ne hjl, add_zero]
    have hf'' : f' ∈ D.grade (∑ j, ((a + Pi.single (M := fun _ : Fin (n + 1) => ℕ) l N) j : ℤ)) := by
      rwa [sum_add_single]
    refine ⟨GradedModule.sec.mk D I ⟨a + Pi.single (M := fun _ : Fin (n + 1) => ℕ) l N, ha', f', hf''⟩, ?_⟩
    show h.secMap I (GradedModule.sec.mk D I _) = GradedModule.sec.mk M I ⟨a, ha, m, hm⟩
    rw [secMap_mk]
    refine (GradedModule.sec_mk_eq M I).mpr ⟨0, fun _ _ => rfl, ?_⟩
    show GradedModule.monMul M (0 + a) (h.toLinearMap f')
      = GradedModule.monMul M (0 + (a + Pi.single (M := fun _ : Fin (n + 1) => ℕ) l N)) m
    rw [zero_add, zero_add, hh, GradedModule.monMul_add_apply, GradedModule.monMul_single]

theorem secMap_injective {h : GradedModule.Hom D M} (hinj : Function.Injective h.toLinearMap)
    (I : Finset (Fin (n + 1))) : Function.Injective (h.secMap I) := by
  intro y y'
  induction y using Quotient.inductionOn with
  | h x =>
    induction y' using Quotient.inductionOn with
    | h x' =>
      intro hxx
      change h.secMap I (GradedModule.sec.mk D I x) = h.secMap I (GradedModule.sec.mk D I x') at hxx
      rw [secMap_mk, secMap_mk, GradedModule.sec_mk_eq] at hxx
      obtain ⟨c, hc, heq⟩ := hxx
      change GradedModule.sec.mk D I x = GradedModule.sec.mk D I x'
      refine (GradedModule.sec_mk_eq D I).mpr ⟨c, hc, hinj ?_⟩
      change GradedModule.monMul M (c + x'.denExp) (h.toLinearMap x.num)
        = GradedModule.monMul M (c + x.denExp) (h.toLinearMap x'.num) at heq
      rwa [← GradedModule.Hom.map_monMul, ← GradedModule.Hom.map_monMul] at heq

theorem cochainMap_apply (h : GradedModule.Hom D M) (i : ℕ) (f : GradedModule.cochain D i) (s : Idx n i) :
    h.cochainMap i f s = h.secMap (Idx.img n s) (f s) := rfl

theorem img_nonempty {i : ℕ} (s : Idx n i) : (Idx.img n s).Nonempty :=
  Finset.card_pos.mp (by rw [Idx.card_img]; exact Nat.succ_pos i)

theorem cochainMap_injective {h : GradedModule.Hom D M} (hinj : Function.Injective h.toLinearMap) (i : ℕ) :
    Function.Injective (h.cochainMap i) := fun f g hfg =>
  funext fun s => secMap_injective hinj _ (by rw [← cochainMap_apply, ← cochainMap_apply, hfg])

theorem cochainMap_surjective {h : GradedModule.Hom D M} (hs : Saturated h) (i : ℕ) :
    Function.Surjective (h.cochainMap i) := fun g => by
  choose f hf using fun s => secMap_surjective hs _ (img_nonempty s) (g s)
  exact ⟨f, funext fun s => by rw [cochainMap_apply, hf]⟩

theorem cochainMap_d (h : GradedModule.Hom D M) (i : ℕ) (f : GradedModule.cochain D i) :
    GradedModule.d M i (h.cochainMap i f) = h.cochainMap (i + 1) (GradedModule.d D i f) := by
  rw [← LinearMap.comp_apply, GradedModule.Hom.cochainMap_comm, LinearMap.comp_apply]

theorem subsingleton_H_succ {h : GradedModule.Hom D M} (hinj : Function.Injective h.toLinearMap) (hs : Saturated h)
    (i : ℕ) (hD : Subsingleton (GradedModule.H D (i + 1))) : Subsingleton (GradedModule.H M (i + 1)) := by
  refine ⟨fun y y' => ?_⟩
  suffices hzero : ∀ z : GradedModule.H M (i + 1), z = 0 by rw [hzero y, hzero y']
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H x =>
    refine (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr ?_)

    obtain ⟨c', hc'⟩ := cochainMap_surjective hs (i + 1) x.1
    have hcyc : GradedModule.d D (i + 1) c' = 0 := by
      apply cochainMap_injective hinj (i + 1 + 1)
      rw [← cochainMap_d, hc', map_zero]
      exact x.2

    have hmk : (Submodule.Quotient.mk ⟨c', LinearMap.mem_ker.mpr hcyc⟩ : GradedModule.H D (i + 1)) = 0 :=
      @Subsingleton.elim _ hD _ _
    obtain ⟨b', hb'⟩ := Submodule.mem_comap.mp ((Submodule.Quotient.mk_eq_zero _).mp hmk)
    refine ⟨h.cochainMap i b', ?_⟩
    show GradedModule.d M i (h.cochainMap i b') = x.1
    rw [cochainMap_d, show GradedModule.d D i b' = c' from hb', hc']

end P2mSatSerreB

theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (M D : ProjSpaceCech.GradedModule R n) (hD : ProjSpaceCech.GradedModule.IsFG D)
    (h : ProjSpaceCech.GradedModule.Hom D M) (hinj : Function.Injective h.toLinearMap)
    (hsat : ∀ (e : ℤ) (f : M.M), f ∈ M.grade e → ∀ j : Fin (n + 1),
      ∃ (N : ℕ) (f' : D.M), f' ∈ D.grade (e + N) ∧ h.toLinearMap f' = (M.xMul j ^ N) f) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift M d) i) := by
  obtain ⟨d₀, hd₀⟩ := ProjSpaceCech.GradedModule.subsingleton_cohomology_shift_of_isFG D hD
  refine ⟨d₀, fun d hd i hi => ?_⟩
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  exact P2mSatSerreB.subsingleton_H_succ (h := h.shift d) hinj (P2mSatSerreB.saturated_shift hsat d) i'
    (hd₀ d hd (i' + 1) hi)

end S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
end P2MW
export P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated (solution)
