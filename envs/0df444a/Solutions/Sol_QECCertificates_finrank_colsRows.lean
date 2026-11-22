-- Prove2me | solution 1 for QECCertificates.finrank_colsRows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:08:46.558528+00:00
-- url     : https://prove2.me/submissions/8c676cd6-aca2-4395-bc5b-66bc6c04e745

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_Basic
public import Definitions.Def_LeanPool_QECCertificates_GF2_KunnethCore
public import Theorems.Thm_QECCertificates_exists_leftInverse_of_linearIndependent
public import Theorems.Thm_QECCertificates_vee_apply
public import Theorems.Thm_QECCertificates_wedge_apply
public import Theorems.Thm_QECCertificates_vee_wedge_of_coords
public import Theorems.Thm_QECCertificates_wedge_vee
public import Theorems.Thm_QECCertificates_rowOf_wedge_mem
public import Theorems.Thm_QECCertificates_rowOf_mem_of_wedge_rowOf_mem
public import Theorems.Thm_QECCertificates_addSmul_apply
public import Theorems.Thm_QECCertificates_add_self
public import Theorems.Thm_QECCertificates_mem_support
attribute [local simp] QECCertificates.addSmul_apply
attribute [local simp] QECCertificates.add_self
attribute [local simp] QECCertificates.mem_support


attribute [local simp] QECCertificates.vee_apply
attribute [local simp] QECCertificates.wedge_apply

set_option autoImplicit true
@[expose] public section
public section
open QECCertificates
open _root_.Matrix
open scoped BigOperators
variable {p q r s a b : ℕ}
namespace QECCertificates
theorem _root_.solution (U : Submodule (ZMod 2) (Vec p)) (W : Submodule (ZMod 2) (Vec s)) :
    Module.finrank (ZMod 2) ↥(colsSub (s := s) U ⊓ rowsSub (s := s) W)
      = Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) W := by
  classical
  let bu : Module.Basis (Fin (Module.finrank (ZMod 2) U)) (ZMod 2) U := Module.finBasis (ZMod 2) U
  let u : Fin (Module.finrank (ZMod 2) U) → Vec p := fun k => (bu k : Vec p)
  have hu : LinearIndependent (ZMod 2) u := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hcU : (∑ k, c k • bu k : U) = 0 := by
      apply Subtype.ext
      simpa [u] using hc
    intro k
    exact Fintype.linearIndependent_iff.mp bu.linearIndependent c hcU k
  obtain ⟨L, hL⟩ := exists_leftInverse_of_linearIndependent hu
  have hcoords : ∀ x ∈ U, ∑ k, L x k • u k = x := by
    intro x hx
    have hspan : x ∈ Submodule.span (ZMod 2) (Set.range u) := by
      have h1 : (⟨x, hx⟩ : U) ∈ Submodule.span (ZMod 2) (Set.range bu) := by
        rw [bu.span_eq]; exact Submodule.mem_top
      obtain ⟨c, hc⟩ :=
        (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := bu)
          (x := (⟨x, hx⟩ : U))).mp h1
      refine (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := u) (x := x)).mpr ⟨c, ?_⟩
      have hval := congrArg (fun y : U => (y : Vec p)) hc
      simpa [u] using hval
    obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank (ZMod 2) U) → ZMod 2, ∑ i, c i • u i = x :=
      (Submodule.mem_span_range_iff_exists_fun (R := ZMod 2) (v := u) (x := x)).mp hspan
    rw [← hc, hL c]
  have hcolW : ∀ f : Fin (Module.finrank (ZMod 2) U) → W,
      ∀ j, colOf (vee u fun kj => ((f kj.1 : W) : Vec s) kj.2) j ∈ U := by
    intro f j
    have hfun : colOf (vee u fun kj => ((f kj.1 : W) : Vec s) kj.2) j
        = ∑ k, (((f k : W) : Vec s) j) • u k := by
      funext i
      rw [colOf_apply, vee_apply, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [Pi.smul_apply, smul_eq_mul]
    rw [hfun]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (show u k ∈ U from (bu k).2)
  have hrowW : ∀ f : Fin (Module.finrank (ZMod 2) U) → W,
      ∀ i, rowOf (vee u fun kj => ((f kj.1 : W) : Vec s) kj.2) i ∈ W := by
    intro f i
    refine rowOf_mem_of_wedge_rowOf_mem hcoords (fun j => hcolW f j) (fun k => ?_) i
    rw [wedge_vee hL]
    exact (f k).2
  have he : ↥(colsSub (s := s) U ⊓ rowsSub (s := s) W) ≃ₗ[ZMod 2]
      (Fin (Module.finrank (ZMod 2) U) → W) :=
    { toFun := fun X => fun k =>
        ⟨rowOf (wedge L X.1) k, rowOf_wedge_mem (X := X.1) (fun i => X.2.2 i) k⟩
      invFun := fun f => ⟨vee u (fun kj => ((f kj.1 : W) : Vec s) kj.2), hcolW f, hrowW f⟩
      left_inv := by
        intro X
        apply Subtype.ext
        exact vee_wedge_of_coords hcoords (fun j => X.2.1 j)
      right_inv := by
        intro f
        funext k
        apply Subtype.ext
        funext j
        simpa using congrFun (wedge_vee (s := s) hL
          (fun kj => ((f kj.1 : W) : Vec s) kj.2)) (k, j)
      map_add' := by
        intro X Y
        funext k
        apply Subtype.ext
        funext j
        change wedge L (X.1 + Y.1) (k, j) = wedge L X.1 (k, j) + wedge L Y.1 (k, j)
        rw [map_add, Pi.add_apply]
      map_smul' := by
        intro c X
        funext k
        apply Subtype.ext
        funext j
        change wedge L (c • X.1) (k, j) = c * wedge L X.1 (k, j)
        rw [map_smul, Pi.smul_apply, smul_eq_mul] }
  rw [he.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  simp
end QECCertificates
