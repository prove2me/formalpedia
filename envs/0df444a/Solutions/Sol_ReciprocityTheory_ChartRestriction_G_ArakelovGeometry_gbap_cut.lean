-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gbap_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:50:34.490364+00:00
-- url     : https://prove2.me/submissions/1cf13d2d-a3a1-4558-a57f-2bc7b9b74fce

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeC
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsSemipositiveOn
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_withBot_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_van_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_gbap_map_map_int
import Theorems.Thm_ReciprocityTheory_AnForm_R_exists_jacobian_cut
import Theorems.Thm_ReciprocityTheory_AnForm_R_extQ_spec
import Theorems.Thm_ReciprocityTheory_AnForm_R_isRegularLocalRing_of_jacobian
import Theorems.Thm_ReciprocityTheory_AnForm_R_ringKrullDim_of_mem_minimalPrimes_extC
import Theorems.Thm_ReciprocityTheory_CA_height_add_ringKrullDim_quotient_mvPolynomial_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open MvPolynomial Module ReciprocityTheory.AnForm.R
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {J : Type} [Fintype J] {D c : ℕ} (e : J ≃ Fin (D + 1 + c))
    (P : Ideal (MvPolynomial J ℤ)) [P.IsPrime]
    (hhor : ∀ m : ℤ, (C m : MvPolynomial J ℤ) ∈ P → m = 0)
    (hdim : ringKrullDim (MvPolynomial J ℤ ⧸ P) = ((D + 1 + 1 : ℕ) : WithBot ℕ∞))
    (z₀ : J → ℂ) (hz₀ : ∀ f ∈ P, eval z₀ (map (Int.castRingHom ℂ) f) = 0)
    (f : Fin c → MvPolynomial J ℤ) (hfP : ∀ i, f i ∈ P)
    (hli : LinearIndependent ℂ
      (fun i => grad (fun j => z₀ (e.symm j)) (map (Int.castRingHom ℂ) (rename e (f i))))) :
    ∃ (F : Fin c → MvPolynomial (Fin (D + 1 + c)) ℂ) (h : MvPolynomial (Fin (D + 1 + c)) ℂ),
      LinearIndependent ℂ (fun i => grad (fun j => z₀ (e.symm j)) (F i)) ∧
      eval (fun j => z₀ (e.symm j)) h ≠ 0 ∧
      ∀ w : Fin (D + 1 + c) → ℂ, eval w h ≠ 0 →
        ((∀ i, eval w (F i) = 0) ↔
          ∀ g ∈ P, eval (fun j => w (e j)) (map (Int.castRingHom ℂ) g) = 0) := by
  classical
  set fe : MvPolynomial J ℤ ≃+* MvPolynomial (Fin (D + 1 + c)) ℤ :=
    (renameEquiv ℤ e).toRingEquiv with hfe
  have hfe_apply : ∀ g, (fe : MvPolynomial J ℤ →+* MvPolynomial (Fin (D + 1 + c)) ℤ) g = rename e g :=
    fun g => rfl
  have hfe_symm : ∀ g, fe.symm g = rename e.symm g := fun g => rfl
  set P' : Ideal (MvPolynomial (Fin (D + 1 + c)) ℤ) :=
    P.map (fe : MvPolynomial J ℤ →+* MvPolynomial (Fin (D + 1 + c)) ℤ) with hP'
  have hP'mem : ∀ g, g ∈ P' ↔ rename e.symm g ∈ P := by
    intro g
    rw [hP', Ideal.map_comap_of_equiv, Ideal.mem_comap]
    rfl
  haveI : P'.IsPrime := by
    rw [hP', Ideal.map_comap_of_equiv]
    infer_instance
  have hP'hor : ∀ m : ℤ, (C m : MvPolynomial (Fin (D + 1 + c)) ℤ) ∈ P' → m = 0 := by
    intro m hm
    rw [hP'mem, rename_C] at hm
    exact hhor m hm
  have hdim' : ringKrullDim (MvPolynomial (Fin (D + 1 + c)) ℤ ⧸ P') =
      ((D + 1 + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← hdim]
    exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P P' fe rfl)).symm
  obtain ⟨hQp, -, hQd⟩ := extQ_spec P' hP'hor
  haveI := hQp
  have hQdim : ringKrullDim (MvPolynomial (Fin (D + 1 + c)) ℚ ⧸ extQ P') =
      ((D + 1 : ℕ) : WithBot ℕ∞) := by
    rw [hdim'] at hQd
    exact gbap_withBot_eq (a := 1) (by exact_mod_cast hQd)
  set K := extC (extQ P') with hK
  have hKvan : ∀ w : Fin (D + 1 + c) → ℂ, (∀ g ∈ K, eval w g = 0) ↔
      ∀ g ∈ P, eval (fun j => w (e j)) (map (Int.castRingHom ℂ) g) = 0 := by
    intro w
    rw [hK, extC, gbap_van_map, extQ]
    constructor
    · intro H g hg
      have := H _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem (fe : MvPolynomial J ℤ →+* MvPolynomial (Fin (D + 1 + c)) ℤ) hg))
      rw [hfe_apply, gbap_map_map_int, map_rename, eval_rename] at this
      exact this
    · intro H g hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        have hy' := (hP'mem y).1 hy
        have := H _ hy'
        rw [gbap_map_map_int]
        have hyy : y = rename e (rename e.symm y) := by
          rw [rename_rename, Equiv.self_comp_symm, rename_id_apply]
        rw [hyy, map_rename, eval_rename]
        exact this
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
      | smul a x _ hx => rw [smul_eq_mul, map_mul, map_mul, hx, mul_zero]
  set p' : Fin (D + 1 + c) → ℂ := fun j => z₀ (e.symm j) with hp'
  have hp'e : (fun j => p' (e j)) = z₀ := by
    funext j
    simp [hp']
  have hp'K : ∀ g ∈ K, eval p' g = 0 := by
    rw [hKvan, hp'e]
    exact hz₀
  have hKle : K ≤ ptIdeal p' := fun g hg => RingHom.mem_ker.2 (hp'K g hg)
  obtain ⟨𝔮, h𝔮min, h𝔮le⟩ := Ideal.exists_minimalPrimes_le hKle
  haveI : 𝔮.IsPrime := h𝔮min.1.1
  have hd𝔮 := ringKrullDim_of_mem_minimalPrimes_extC (extQ P') 𝔮 h𝔮min
  have hht := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field ℂ (D + 1 + c) 𝔮
  rw [hd𝔮, hQdim] at hht
  have hht' : (𝔮.height : WithBot ℕ∞) = (c : WithBot ℕ∞) :=
    gbap_withBot_eq (a := D + 1) (by rw [hht]; congr 1; omega)
  have hhtc : 𝔮.height ≤ c := by
    have : 𝔮.height = (c : ℕ∞) := by exact_mod_cast hht'
    rw [this]
  set F0 : Fin c → MvPolynomial (Fin (D + 1 + c)) ℂ :=
    fun i => map (Int.castRingHom ℂ) (rename e (f i)) with hF0
  have hF0K : ∀ i, F0 i ∈ K := by
    intro i
    have h1 : rename e (f i) ∈ P' :=
      Ideal.mem_map_of_mem (fe : MvPolynomial J ℤ →+* MvPolynomial (Fin (D + 1 + c)) ℤ) (hfP i)
    have := Ideal.mem_map_of_mem (map (algebraMap ℚ ℂ))
      (Ideal.mem_map_of_mem (map (Int.castRingHom ℚ)) h1)
    rw [gbap_map_map_int] at this
    exact this
  have hreg := isRegularLocalRing_of_jacobian K p' hp'K F0 hF0K hli ⟨𝔮, h𝔮min, h𝔮le, hhtc⟩
  haveI := hreg.1
  have hcc : D + 1 + c - (D + 1) = c := by omega
  obtain ⟨-, F', hF'K, hF'li, h, hh, hspan⟩ :=
    exists_jacobian_cut K p' (D + 1) (by rw [hreg.2]; congr 2; omega)
  refine ⟨fun i => F' (Fin.cast hcc.symm i), h, ?_, hh, ?_⟩
  · exact hF'li.comp _ (Fin.cast_injective _)
  · intro w hw
    rw [← hKvan]
    constructor
    · intro H g hg
      have hsp : Ideal.span (Set.range F') ≤ RingHom.ker (eval w) := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        have := H (Fin.cast hcc j)
        simp only [Fin.cast_cast, Fin.cast_eq_self] at this
        exact RingHom.mem_ker.2 this
      have := RingHom.mem_ker.1 (hsp (hspan g hg))
      rw [map_mul] at this
      exact (mul_eq_zero.1 this).resolve_left hw
    · intro H i
      exact H _ (hF'K _)
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
