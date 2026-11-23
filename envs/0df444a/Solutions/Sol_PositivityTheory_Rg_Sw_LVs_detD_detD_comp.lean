-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.detD_detD_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:23.668804+00:00
-- url     : https://prove2.me/submissions/8f87cde2-6ebd-4265-bb2c-df8d4534d2a3

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
namespace PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
private theorem contDiffOn_iteratedFDeriv_apply {E G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] (F : E → G) (U : Set E) (hU : IsOpen U)
    (hF : ContDiffOn ℂ ∞ F U) (b : ℕ) (w : Fin b → E) :
    ContDiffOn ℂ ∞ (fun y => iteratedFDeriv ℂ b F y w) U := by
  intro y hy
  have h := (hF.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right (i := b) (m := ∞)
    (by exact_mod_cast le_top)
  exact ((ContinuousMultilinearMap.apply ℂ (fun _ : Fin b => E) G w).contDiff.contDiffAt.comp y h).contDiffWithinAt
private theorem iteratedFDeriv_add_append_eq_iteratedFDeriv_apply {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (a b : ℕ) :
    ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] (F : E → G) (U : Set E), IsOpen U →
      ContDiffOn ℂ ∞ F U → ∀ x ∈ U, ∀ (u : Fin a → E) (w : Fin b → E),
      iteratedFDeriv ℂ (a + b) F x (Fin.append u w) =
        iteratedFDeriv ℂ a (fun y => iteratedFDeriv ℂ b F y w) x u := by
  induction b with
  | zero =>
    intro G _ _ F U hU hF x hx u w
    have hw : Fin.append u w = u := by
      funext i
      exact Fin.append_left u w i
    rw [hw]
    simp only [iteratedFDeriv_zero_apply]
    rfl
  | succ b ih =>
    intro G _ _ F U hU hF x hx u w
    have hF' : ContDiffOn ℂ ∞ (fderiv ℂ F) U := hF.fderiv_of_isOpen hU (by exact_mod_cast le_top)
    let v : Fin (a + b + 1) → E := @Fin.append a (b + 1) E u w
    have h1 : iteratedFDeriv ℂ (a + (b + 1)) F x (Fin.append u w) =
        iteratedFDeriv ℂ (a + b) (fun y => fderiv ℂ F y) x (Fin.init v) (v (Fin.last (a + b))) :=
      iteratedFDeriv_succ_apply_right v
    have hinit : Fin.init v = Fin.append u (Fin.init w) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]
        exact Fin.append_left u w j
      · rw [Fin.append_right]
        exact Fin.append_right u w j.castSucc
    have hlast : v (Fin.last (a + b)) = w (Fin.last b) := Fin.append_right u w (Fin.last b)
    rw [h1, hinit, hlast, ih (fderiv ℂ F) U hU hF' x hx u (Fin.init w)]
    have hfun : (fun y => iteratedFDeriv ℂ (b + 1) F y w) =
        (ContinuousLinearMap.apply ℂ G (w (Fin.last b))) ∘
          (fun y => iteratedFDeriv ℂ b (fun z => fderiv ℂ F z) y (Fin.init w)) := by
      funext y
      simp [iteratedFDeriv_succ_apply_right]
    have hs : ContDiffAt ℂ ∞ (fun y => iteratedFDeriv ℂ b (fun z => fderiv ℂ F z) y (Fin.init w)) x :=
      (contDiffOn_iteratedFDeriv_apply (fderiv ℂ F) U hU hF' b (Fin.init w)).contDiffAt (hU.mem_nhds hx)
    rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_left _ hs (by exact_mod_cast le_top)]
    rfl
private theorem iteratedFDeriv_comp_add_clm_zero {E E' G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (F : E → G) (U : Set E) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (y : E) (hy : y ∈ U)
    (L : E' →L[ℂ] E) (b : ℕ) (v : Fin b → E') :
    iteratedFDeriv ℂ b (fun S => F (y + L S)) 0 v = iteratedFDeriv ℂ b F y (fun i => L (v i)) := by
  let F' : E → G := fun z => F (y + z)
  let U' : Set E := {z | y + z ∈ U}
  have hU' : IsOpen U' := hU.preimage (continuous_const.add continuous_id)
  have hF' : ContDiffOn ℂ ∞ F' U' :=
    hF.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz)
  have h0 : L 0 ∈ U' := by
    show y + L 0 ∈ U
    simpa using hy
  have hpre : IsOpen (L ⁻¹' U') := hU'.preimage L.continuous
  have key := L.iteratedFDerivWithin_comp_right hF' hU'.uniqueDiffOn hpre.uniqueDiffOn h0 (i := b)
    (by exact_mod_cast le_top)
  have e1 : iteratedFDerivWithin ℂ b (F' ∘ L) (L ⁻¹' U') 0 = iteratedFDeriv ℂ b (F' ∘ L) 0 :=
    iteratedFDerivWithin_of_isOpen b hpre h0
  have e2 : iteratedFDerivWithin ℂ b F' U' (L 0) = iteratedFDeriv ℂ b F' (L 0) :=
    iteratedFDerivWithin_of_isOpen b hU' h0
  have key2 : iteratedFDeriv ℂ b (F' ∘ L) 0 =
      (iteratedFDeriv ℂ b F' (L 0)).compContinuousLinearMap fun _ => L := by
    rw [← e1, ← e2]
    exact key
  have e3 : iteratedFDeriv ℂ b F' (L 0) = iteratedFDeriv ℂ b F y := by
    have := iteratedFDerivWithin_comp_add_left (𝕜 := ℂ) (f := F) (s := Set.univ) b y (L 0)
    simp only [iteratedFDerivWithin_univ, Set.vadd_set_univ, map_zero, add_zero] at this
    rw [map_zero]
    exact this
  have hfun : (fun S => F (y + L S)) = F' ∘ L := rfl
  rw [hfun, key2, e3]
  rfl
end PositivityTheory.Rg.Sw.LVs
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (F : M2 n → ℂ) (U : Set (M2 n)) (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U) (x₀ : M2 n) (hx : x₀ ∈ U)
    (LA : Matrix ιA ιA ℂ →L[ℂ] M2 n) (LB : Matrix ιB ιB ℂ →L[ℂ] M2 n) :
    detD (fun T : Matrix ιA ιA ℂ => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) =
      ∑ σ : Equiv.Perm ιA, ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign σ : ℂ) * (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) F x₀
          (Fin.append (fun i => LA (Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1))
            (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
  have hΨ : ∀ τ : Equiv.Perm ιB, ContDiffOn ℂ ∞ (fun y => iteratedFDeriv ℂ (Fintype.card ιB) F y
      (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) U :=
    fun τ => contDiffOn_iteratedFDeriv_apply F U hU hF _ _
  have hx' : x₀ + LA 0 ∈ U := by simpa using hx
  have hev : (fun T => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) =ᶠ[nhds 0]
      (fun T => ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
        (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
    have hopen : IsOpen {T : Matrix ιA ιA ℂ | x₀ + LA T ∈ U} :=
      hU.preimage (continuous_const.add LA.continuous)
    filter_upwards [hopen.mem_nhds hx'] with T hT
    simp only [detD]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    exact congrArg _ (iteratedFDeriv_comp_add_clm_zero F U hU hF (x₀ + LA T) hT LB _ _)
  have hD : iteratedFDeriv ℂ (Fintype.card ιA) (fun T => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))) 0 =
      iteratedFDeriv ℂ (Fintype.card ιA) (fun T => ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) 0 := by
    have h2 := hev
    rw [← nhdsWithin_univ] at h2
    have := h2.iteratedFDerivWithin_eq (𝕜 := ℂ) hev.eq_of_nhds (Fintype.card ιA)
    simpa only [iteratedFDerivWithin_univ] using this
  have hsum : ∀ u : Fin (Fintype.card ιA) → Matrix ιA ιA ℂ,
      iteratedFDeriv ℂ (Fintype.card ιA) (fun T => ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) *
        iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) 0 u =
      ∑ τ : Equiv.Perm ιB, (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιA + Fintype.card ιB) F x₀
        (Fin.append (fun i => LA (u i))
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
    intro u
    have hcd' : ∀ τ : Equiv.Perm ιB, ContDiffAt ℂ (Fintype.card ιA) (fun T => iteratedFDeriv ℂ (Fintype.card ιB) F
        (x₀ + LA T) (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i)
          (τ ((Fintype.equivFin ιB).symm i)) 1))) 0 := by
      intro τ
      have h1 := (hΨ τ).contDiffAt (hU.mem_nhds hx')
      have h2 : ContDiffAt ℂ ∞ (fun T : Matrix ιA ιA ℂ => x₀ + LA T) 0 :=
        (contDiff_const.add LA.contDiff).contDiffAt
      refine (h1.comp 0 h2).of_le ?_
      exact_mod_cast le_top
    have hcd : ∀ τ ∈ (Finset.univ : Finset (Equiv.Perm ιB)), ContDiffAt ℂ (Fintype.card ιA)
        (fun T => (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) 0 :=
      fun τ _ => contDiffAt_const.mul (hcd' τ)
    rw [iteratedFDeriv_fun_sum_apply hcd, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    have hfun : (fun T => (Equiv.Perm.sign τ : ℂ) * iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) =
        (Equiv.Perm.sign τ : ℂ) • (fun T => iteratedFDeriv ℂ (Fintype.card ιB) F (x₀ + LA T)
          (fun i => LB (Matrix.single ((Fintype.equivFin ιB).symm i) (τ ((Fintype.equivFin ιB).symm i)) 1))) := by
      funext T
      simp
    rw [hfun, iteratedFDeriv_const_smul_apply (hcd' τ), ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    congr 1
    exact (iteratedFDeriv_comp_add_clm_zero _ U hU (hΨ τ) x₀ hx LA _ _).trans
      (iteratedFDeriv_add_append_eq_iteratedFDeriv_apply _ _ F U hU hF x₀ hx _ _).symm
  have hdef : ∀ G : Matrix ιA ιA ℂ → ℂ, detD G = ∑ σ : Equiv.Perm ιA, (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ (Fintype.card ιA) G 0
        (fun i => Matrix.single ((Fintype.equivFin ιA).symm i) (σ ((Fintype.equivFin ιA).symm i)) 1) :=
    fun G => rfl
  rw [hdef (fun T => detD (fun S : Matrix ιB ιB ℂ => F (x₀ + LA T + LB S))), hD]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  ring
end PositivityTheory.Rg.Sw.LVs
