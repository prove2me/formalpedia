-- Prove2me | solution 1 for ProjSpaceCech.GradedModule.nonempty_HEquiv_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/1c6f204c-c28e-5c93-81b7-2118dfade426

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi

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
p2m_export "ProjSpaceCech" "Idx Idx.img Idx.face Idx.img_face_subset GradedModule GradedModule.monMul GradedModule.monMul_add_apply GradedModule.monMul_mem_grade GradedModule.Frac GradedModule.sec GradedModule.sec.mk GradedModule.sec_mk_eq GradedModule.secIncl GradedModule.cochain GradedModule.faceRes GradedModule.d GradedModule.d_apply GradedModule.H GradedModule.pi"
p2m_open "ProjSpaceCech"

section PiHelpers

variable {R : Type u} [CommRing R]

namespace GradedModule p2m_export "ProjSpaceCech.GradedModule" "monMul monMul_add_apply monMul_mem_grade Frac sec sec.mk sec_mk_eq secIncl cochain faceRes d d_apply H pi mk M xMul" end GradedModule
p2m_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.piComm {α : Type*} {β : Type*} (M : α → β → Type*)
    [∀ a b, AddCommMonoid (M a b)] [∀ a b, Module R (M a b)] :
    (∀ a, ∀ b, M a b) ≃ₗ[R] (∀ b, ∀ a, M a b) where
  toFun f b a := f a b
  invFun g a b := g b a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

p2m_open_scoped "ProjSpaceCech.GradedModule" in
theorem GradedModule.piComm_apply {α : Type*} {β : Type*} (M : α → β → Type*)
    [∀ a b, AddCommMonoid (M a b)] [∀ a b, Module R (M a b)]
    (f : ∀ a, ∀ b, M a b) (b : β) (a : α) :
    GradedModule.piComm (R := R) M f b a = f a b := by
  rfl

p2m_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.piSubmodEquiv {ι : Type*} {M : ι → Type*}
    [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)] (p : ∀ k, Submodule R (M k)) :
    ↥(Submodule.pi Set.univ p) ≃ₗ[R] (∀ k, ↥(p k)) where
  toFun f k := ⟨f.1 k, f.2 k (Set.mem_univ k)⟩
  invFun g := ⟨fun k => (g k).1, fun k _ => (g k).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

p2m_open_scoped "ProjSpaceCech.GradedModule" in
theorem GradedModule.piSubmodEquiv_apply_coe {ι : Type*} {M : ι → Type*}
    [∀ k, AddCommMonoid (M k)] [∀ k, Module R (M k)] (p : ∀ k, Submodule R (M k))
    (f : ↥(Submodule.pi Set.univ p)) (k : ι) :
    ((GradedModule.piSubmodEquiv (R := R) p f k : M k)) = (f : ∀ k, M k) k := by
  rfl

end PiHelpers

section PiEquiv

variable {R : Type u} [CommRing R] {n : ℕ}
variable {ι : Type} [Fintype ι] (D : ι → GradedModule R n)

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.pi_monMul_apply (a : Fin (n + 1) → ℕ)
    (m : ∀ k, (D k).M) (k : ι) :
    GradedModule.monMul (GradedModule.pi D) a m k = GradedModule.monMul (D k) a (m k) := by
  suffices h : ∀ (s : Finset (Fin (n + 1))) (hc : _) (hc' : _),
      (s.noncommProd (fun j => (GradedModule.pi D).xMul j ^ a j) hc) m k
        = (s.noncommProd (fun j => (D k).xMul j ^ a j) hc') (m k) from h Finset.univ _ _
  intro s
  induction s using Finset.induction with
  | empty => intro _ _; simp
  | insert j s hj ih =>
    intro hc hc'
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hj,
      Finset.noncommProd_insert_of_notMem _ _ _ _ hj, Module.End.mul_apply, Module.End.mul_apply]
    have hih := ih (hc.mono (by simp [Finset.subset_insert]))
      (hc'.mono (by simp [Finset.subset_insert]))

    induction a j with
    | zero => simpa using hih
    | succ p ihp =>
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      exact congrArg ((D k).xMul j) ihp

p2m_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.secPiProj (I : Finset (Fin (n + 1))) (k : ι) :
    GradedModule.sec (GradedModule.pi D) I →ₗ[R] GradedModule.sec (D k) I where
  toFun := Quotient.map
    (fun x => ⟨x.denExp, x.hden, x.num k, x.hnum k (Set.mem_univ k)⟩)
    (fun _ _ ⟨c, hc, heq⟩ => ⟨c, hc, by
      have h1 := congrFun heq k
      simp only [GradedModule.pi_monMul_apply] at h1; exact h1⟩)
  map_add' := by
    rintro ⟨x⟩ ⟨y⟩
    refine (GradedModule.sec_mk_eq _ I).mpr ⟨0, fun _ _ => rfl, ?_⟩
    have hnum : ((GradedModule.monMul (GradedModule.pi D) y.denExp) x.num
            + (GradedModule.monMul (GradedModule.pi D) x.denExp) y.num) k
          = (GradedModule.monMul (D k) y.denExp) (x.num k)
            + (GradedModule.monMul (D k) x.denExp) (y.num k) := by
      change (_ : (D k).M) + _ = _
      rw [GradedModule.pi_monMul_apply, GradedModule.pi_monMul_apply]
    simp only [zero_add, hnum, map_add]
  map_smul' := by
    rintro r ⟨x⟩
    refine (GradedModule.sec_mk_eq _ I).mpr ⟨0, fun _ _ => rfl, ?_⟩
    have hnum : (r • x.num) k = r • (x.num k : (D k).M) := rfl
    simp only [zero_add, hnum, map_smul, RingHom.id_apply]

p2m_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.secPiFwd (I : Finset (Fin (n + 1))) :
    GradedModule.sec (GradedModule.pi D) I
      →ₗ[R] (∀ k, GradedModule.sec (D k) I) :=
  LinearMap.pi (GradedModule.secPiProj D I)

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.secPiFwd_incl {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) :
    (LinearMap.pi (fun k => (GradedModule.secIncl (D k) hIJ).comp (LinearMap.proj k))).comp
        (GradedModule.secPiFwd D I)
      = (GradedModule.secPiFwd D J).comp
          (GradedModule.secIncl (GradedModule.pi D) hIJ) := by
  refine LinearMap.ext fun z => funext fun k => ?_
  obtain ⟨x⟩ := z; rfl

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.secPiFwd_injective (I : Finset (Fin (n + 1))) :
    Function.Injective (GradedModule.secPiFwd D I) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨x⟩ := z
  have hk : ∀ k, ∃ (c : Fin (n + 1) → ℕ),
      (∀ j ∉ I, c j = 0) ∧ GradedModule.monMul (D k) c (x.num k) = 0 := by
    intro k
    have hzk := congrFun hz k
    simp only [GradedModule.secPiFwd, GradedModule.secPiProj, LinearMap.pi_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at hzk
    have hrel := (GradedModule.sec_mk_eq (D k) I).mp hzk
    obtain ⟨c, hc, heq⟩ := hrel
    exact ⟨c, hc, by simpa using heq⟩
  classical
  choose c hc hcz using hk
  refine (GradedModule.sec_mk_eq _ I).mpr ⟨∑ k, c k, ?_, ?_⟩
  · intro j hj; simp only [Finset.sum_apply]
    exact Finset.sum_eq_zero fun k _ => hc k j hj
  · simp only [add_zero, map_zero]
    funext k
    rw [GradedModule.pi_monMul_apply]
    show (GradedModule.monMul (D k) (∑ k', c k')) (x.num k) = 0
    have heq : (∑ k', c k') = (∑ k' ∈ Finset.univ.erase k, c k') + c k := by
      ext j; simp only [Pi.add_apply, Finset.sum_apply]
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ k)).symm
    rw [heq, GradedModule.monMul_add_apply, hcz, map_zero]

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.secPiFwd_surjective (I : Finset (Fin (n + 1))) :
    Function.Surjective (GradedModule.secPiFwd D I) := by
  intro z
  classical
  have hk : ∀ k, ∃ x : GradedModule.Frac (D k) I, z k = GradedModule.sec.mk (D k) I x :=
    fun k => Quotient.exists_rep (z k) |>.imp fun x hx => hx.symm
  choose x hx using hk
  set a : Fin (n + 1) → ℕ := ∑ k, (x k).denExp with ha_def
  have haI : ∀ j ∉ I, a j = 0 := fun j hj => by
    simp only [ha_def, Finset.sum_apply]
    exact Finset.sum_eq_zero fun k _ => (x k).hden j hj
  have hax : ∀ k, ∃ (c : Fin (n + 1) → ℕ), (∀ j ∉ I, c j = 0) ∧ c + (x k).denExp = a := by
    intro k
    refine ⟨∑ k' ∈ Finset.univ.erase k, (x k').denExp, fun j hj => ?_, ?_⟩
    · simp only [Finset.sum_apply]
      exact Finset.sum_eq_zero fun k' _ => (x k').hden j hj
    · ext j; simp only [Pi.add_apply, Finset.sum_apply, ha_def]
      exact Finset.sum_erase_add _ _ (Finset.mem_univ k)
  choose c hc hca using hax
  refine ⟨GradedModule.sec.mk _ I ⟨a, haI,
    fun k => GradedModule.monMul (D k) (c k) ((x k).num), fun k _ => ?_⟩, ?_⟩
  · have h := GradedModule.monMul_mem_grade (D k) (c k) _ (x k).num (x k).hnum
    have hgrade : (∑ j, (a j : ℤ))
        = (∑ j, ((x k).denExp j : ℤ)) + (∑ j, ((c k) j : ℤ)) := by
      have hsum := congrArg (fun f => ∑ j, (f j : ℤ)) (hca k).symm
      simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib] at hsum
      linarith
    rwa [← hgrade] at h
  · funext k
    simp only [GradedModule.secPiFwd, GradedModule.secPiProj, LinearMap.pi_apply,
      LinearMap.coe_mk, AddHom.coe_mk, hx]
    refine ((GradedModule.sec_mk_eq (D k) I).mpr ⟨0, fun _ _ => rfl, ?_⟩)
    show GradedModule.monMul (D k) (0 + (x k).denExp)
        (GradedModule.monMul (D k) (c k) ((x k).num))
      = GradedModule.monMul (D k) (0 + a) ((x k).num)
    rw [zero_add, zero_add, ← GradedModule.monMul_add_apply, add_comm, hca k]

p2m_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.secPiEquiv (I : Finset (Fin (n + 1))) :
    GradedModule.sec (GradedModule.pi D) I ≃ₗ[R] (∀ k, GradedModule.sec (D k) I) :=
  LinearEquiv.ofBijective (GradedModule.secPiFwd D I)
    ⟨GradedModule.secPiFwd_injective D I, GradedModule.secPiFwd_surjective D I⟩

p2m_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.cochainPiEquiv (i : ℕ) :
    GradedModule.cochain (GradedModule.pi D) i
      ≃ₗ[R] (∀ k, GradedModule.cochain (D k) i) :=
  (LinearEquiv.piCongrRight fun s => GradedModule.secPiEquiv D (Idx.img n s)).trans
    (GradedModule.piComm (R := R) _)

p2m_open_scoped "ProjSpaceCech.GradedModule" in
theorem GradedModule.cochainPiEquiv_apply (i : ℕ)
    (f : GradedModule.cochain (GradedModule.pi D) i)
    (k : ι) (s : Idx n i) :
    GradedModule.cochainPiEquiv D i f k s
      = GradedModule.secPiFwd D (Idx.img n s) (f s) k := by
  rfl

p2m_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.piAltd (i : ℕ) :
    (∀ k, GradedModule.cochain (D k) i) →ₗ[R] (∀ k, GradedModule.cochain (D k) (i + 1)) :=
  LinearMap.pi fun k => (GradedModule.d (D k) i).comp (LinearMap.proj k)

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.cochainPiEquiv_comm (i : ℕ) :
    (GradedModule.piAltd D i).comp (GradedModule.cochainPiEquiv D i).toLinearMap
      = (GradedModule.cochainPiEquiv D (i + 1)).toLinearMap.comp
          (GradedModule.d (GradedModule.pi D) i) := by
  refine LinearMap.ext fun f => funext fun k => funext fun s => ?_
  simp only [LinearMap.comp_apply, GradedModule.piAltd, LinearMap.pi_apply, LinearMap.proj_apply,
    LinearEquiv.coe_toLinearMap, GradedModule.cochainPiEquiv_apply,
    GradedModule.d_apply, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    GradedModule.secPiFwd, GradedModule.faceRes]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact congrArg (((-1 : R) ^ (j : ℕ)) • ·)
    (congrFun (LinearMap.congr_fun
      (GradedModule.secPiFwd_incl D (Idx.img_face_subset n s j))
      (f (Idx.face n s j))) k)

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.cochainPiEquiv_ker (i : ℕ) :
    (LinearMap.ker (GradedModule.d (GradedModule.pi D) i)).map
        (GradedModule.cochainPiEquiv D i).toLinearMap
      = LinearMap.ker (GradedModule.piAltd D i) := by
  have hcomm := GradedModule.cochainPiEquiv_comm D i
  have hcomap : (LinearMap.ker (GradedModule.piAltd D i)).comap
      (GradedModule.cochainPiEquiv D i).toLinearMap
        = LinearMap.ker (GradedModule.d (GradedModule.pi D) i) := by
    rw [← LinearMap.ker_comp, hcomm, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
  rw [← hcomap, Submodule.map_comap_eq_of_surjective
    (GradedModule.cochainPiEquiv D i).surjective]

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.cochainPiEquiv_range (i : ℕ) :
    (LinearMap.range (GradedModule.d (GradedModule.pi D) i)).map
        (GradedModule.cochainPiEquiv D (i + 1)).toLinearMap
      = LinearMap.range (GradedModule.piAltd D i) := by
  rw [LinearMap.range_eq_map, ← Submodule.map_comp,
    ← GradedModule.cochainPiEquiv_comm D i, Submodule.map_comp, Submodule.map_top,
    LinearEquiv.range, Submodule.map_top]

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.ker_piAltd (i : ℕ) :
    LinearMap.ker (GradedModule.piAltd D i)
      = Submodule.pi Set.univ (fun k => LinearMap.ker (GradedModule.d (D k) i)) := by
  ext f
  simp only [LinearMap.mem_ker, GradedModule.piAltd, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.mem_pi, Set.mem_univ, forall_true_left, funext_iff,
    Pi.zero_apply]

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.range_piAltd (i : ℕ) :
    LinearMap.range (GradedModule.piAltd D i)
      = Submodule.pi Set.univ (fun k => LinearMap.range (GradedModule.d (D k) i)) := by
  refine le_antisymm ?_ ?_
  · rintro g ⟨f, rfl⟩ k _; exact ⟨f k, rfl⟩
  · intro g hg
    classical
    have hk : ∀ k, ∃ f, GradedModule.d (D k) i f = g k :=
      fun k => hg k (Set.mem_univ k)
    choose f hf using hk
    exact ⟨f, funext hf⟩

p2m_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.kerPiEquiv (i : ℕ) :
    ↥(LinearMap.ker (GradedModule.d (GradedModule.pi D) i))
      ≃ₗ[R] (∀ k, ↥(LinearMap.ker (GradedModule.d (D k) i))) :=
  (((GradedModule.cochainPiEquiv D i).submoduleMap _).trans
    (LinearEquiv.ofEq _ _
      ((GradedModule.cochainPiEquiv_ker D i).trans (GradedModule.ker_piAltd D i)))).trans
    (GradedModule.piSubmodEquiv (R := R) _)

p2m_open_scoped "ProjSpaceCech.GradedModule" in
theorem GradedModule.kerPiEquiv_apply_coe (i : ℕ)
    (x : ↥(LinearMap.ker (GradedModule.d (GradedModule.pi D) i))) (k : ι) :
    (GradedModule.kerPiEquiv D i x k).1
      = GradedModule.cochainPiEquiv D i x.1 k := by
  have hstep := LinearEquiv.coe_ofEq_apply (M := ∀ k, GradedModule.cochain (D k) i)
    ((GradedModule.cochainPiEquiv_ker D i).trans (GradedModule.ker_piAltd D i))
    (((GradedModule.cochainPiEquiv D i).submoduleMap
      (LinearMap.ker (GradedModule.d (GradedModule.pi D) i))) x)
  simp only [GradedModule.kerPiEquiv, LinearEquiv.trans_apply]
  calc (GradedModule.piSubmodEquiv (R := R)
          (fun k => LinearMap.ker (GradedModule.d (D k) i)) _ k).1
      = (((LinearEquiv.ofEq _ _ _)
          (((GradedModule.cochainPiEquiv D i).submoduleMap _) x)
            : ↥(Submodule.pi Set.univ _)).1 : ∀ k, GradedModule.cochain (D k) i) k := rfl
    _ = (((GradedModule.cochainPiEquiv D i).submoduleMap _) x
            : ∀ k, GradedModule.cochain (D k) i) k := by rw [hstep]
    _ = GradedModule.cochainPiEquiv D i x.1 k := by
          rw [LinearEquiv.submoduleMap_apply]

p2m_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.kerPiEquiv_comap_range (j : ℕ) :
    Submodule.map (GradedModule.kerPiEquiv D (j + 1)).toLinearMap
        ((LinearMap.range (GradedModule.d (GradedModule.pi D) j)).comap
          (LinearMap.ker (GradedModule.d (GradedModule.pi D) (j + 1))).subtype)
      = Submodule.pi Set.univ (fun k =>
          (LinearMap.range (GradedModule.d (D k) j)).comap
            (LinearMap.ker (GradedModule.d (D k) (j + 1))).subtype) := by

  have hmain : ∀ (y : GradedModule.cochain (GradedModule.pi D) (j + 1)),
      y ∈ LinearMap.range (GradedModule.d (GradedModule.pi D) j)
        ↔ ∀ k, GradedModule.cochainPiEquiv D (j + 1) y k
            ∈ LinearMap.range (GradedModule.d (D k) j) := by
    intro y
    have hstep : (∀ k, GradedModule.cochainPiEquiv D (j + 1) y k
        ∈ LinearMap.range (GradedModule.d (D k) j))
          ↔ GradedModule.cochainPiEquiv D (j + 1) y
              ∈ LinearMap.range (GradedModule.piAltd D j) := by
      rw [GradedModule.range_piAltd]
      exact ⟨fun h k _ => h k, fun h k => h k (Set.mem_univ k)⟩
    rw [hstep, ← GradedModule.cochainPiEquiv_range D j, Submodule.mem_map_equiv,
      LinearEquiv.symm_apply_apply]
  refine le_antisymm ?_ ?_
  · rw [Submodule.map_le_iff_le_comap]
    rintro ⟨y, hy⟩ hyr
    simp only [Submodule.mem_comap, Submodule.coe_subtype] at hyr
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, Submodule.mem_pi, Set.mem_univ,
      forall_true_left]
    intro k
    show (GradedModule.kerPiEquiv D (j + 1) ⟨y, hy⟩ k).1
      ∈ LinearMap.range (GradedModule.d (D k) j)
    rw [GradedModule.kerPiEquiv_apply_coe]
    exact (hmain y).mp hyr k
  · intro z hz
    obtain ⟨⟨y, hy⟩, hyz⟩ := (GradedModule.kerPiEquiv D (j + 1)).surjective z
    refine ⟨⟨y, hy⟩, ?_, hyz⟩
    show y ∈ LinearMap.range (GradedModule.d (GradedModule.pi D) j)
    refine (hmain y).mpr fun k => ?_
    rw [← GradedModule.kerPiEquiv_apply_coe D (j + 1) ⟨y, hy⟩ k]
    have hzk := hz k (Set.mem_univ k)
    rw [← hyz] at hzk
    simp only [Submodule.mem_comap, Submodule.coe_subtype] at hzk
    exact hzk

p2m_open_scoped "ProjSpaceCech.GradedModule" in

def GradedModule.HPiEquiv (i : ℕ) :
    GradedModule.H (GradedModule.pi D) i ≃ₗ[R] (∀ k, GradedModule.H (D k) i) := by
  classical
  rcases i with _ | j
  ·
    exact GradedModule.kerPiEquiv D 0
  ·
    exact (Submodule.Quotient.equiv _ _ (GradedModule.kerPiEquiv D (j + 1))
        (GradedModule.kerPiEquiv_comap_range D j)).trans
      (Submodule.quotientPi (R := R)
        (fun k => (LinearMap.range (GradedModule.d (D k) j)).comap
          (LinearMap.ker (GradedModule.d (D k) (j + 1))).subtype))

end PiEquiv

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι] (D : ι → ProjSpaceCech.GradedModule R n) (i : ℕ) :
    Nonempty (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.pi D) i ≃ₗ[R] (∀ k, ProjSpaceCech.GradedModule.H (D k) i)) :=
  ⟨ProjSpaceCech.GradedModule.HPiEquiv D i⟩

end

end S_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi
end P2MW
export P2MW.S_ProjSpaceCech_GradedModule_nonempty_HEquiv_pi (solution)
