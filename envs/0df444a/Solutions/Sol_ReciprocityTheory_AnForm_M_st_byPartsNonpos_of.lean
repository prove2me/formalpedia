-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.st_byPartsNonpos_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:38:10.634682+00:00
-- url     : https://prove2.me/submissions/f7a00781-e59c-4084-8745-5e0378ed0048

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_StokesD
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_nonpos_piece
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_stokes_of
import Theorems.Thm_ReciprocityTheory_AnForm_M_isPotential_ofFun
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntLinear
import Theorems.Thm_ReciprocityTheory_AnForm_M_mIntegrableCont
import Theorems.Thm_ReciprocityTheory_AnForm_M_smoothOnAlg
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_exists_good_partition
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_smooth_continuous
import Theorems.Thm_ReciprocityTheory_AnForm_M_st_smooth_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
section Leibniz
variable {D : ℕ}
end Leibniz
variable {e : ℕ} {X : Type} [TopologicalSpace X]
section Piece
variable [CompactSpace X] [T2Space X] (A : FinHolAtlas (e + 1) X) (Φ : Fin e → LocPot X)
  (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin A.n) (G : Set X) (hGo : IsOpen G)
  (hG : G ⊆ (A.chart j).source) (x0 : Fin e → X) (hGU : ∀ i, G ⊆ (Φ i).U (x0 i))
end Piece
private theorem mInt_finset_sum [CompactSpace X] [T2Space X] {d : ℕ} (A : FinHolAtlas d X)
    (Ψ : Fin d → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) {M : ℕ} (f : Fin M → X → ℝ)
    (hf : ∀ m, Continuous (f m)) (s : Finset (Fin M)) :
    mInt A Ψ (fun x => ∑ m ∈ s, f m x) = ∑ m ∈ s, mInt A Ψ (f m) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := mIntLinear A Ψ hΨ (-1) (fun _ => 0) (fun _ => 0)
      (mIntegrableCont A Ψ hΨ _ continuous_const) (mIntegrableCont A Ψ hΨ _ continuous_const)
    simp only [mul_zero, add_zero] at h
    simp only [Finset.sum_empty]
    linarith
  | insert a s ha ih =>
    have h := mIntLinear A Ψ hΨ 1 (f a) (fun x => ∑ m ∈ s, f m x)
      (mIntegrableCont A Ψ hΨ _ (hf a))
      (mIntegrableCont A Ψ hΨ _ (continuous_finset_sum _ fun m _ => hf m))
    simp only [one_mul] at h
    simp only [Finset.sum_insert ha]
    rw [h, ih]
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology Set
open ReciprocityTheory.AnForm.A
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (hP : PartsStatement) (hN : GradDensNonnegStatement) :
    ByPartsNonposStatement := by
  intro e X _ _ _ A v hv Φ hΦ hpsh
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := by
    first
    | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    | exact WithTop.coe_le_coe.mpr le_top
    | norm_num
    | simp
  obtain ⟨M, θ, G, j, x0, hθs, hθ0, hθ1, hθG, hGo, hGs, hGU⟩ := st_exists_good_partition A Φ
  have hvc := st_smooth_continuous A hv
  have hvv : A.Smooth (fun x => v x * v x) := st_smooth_mul A hv hv
  have hv2 : A.Smooth (fun x => 1 / 2 * (v x * v x)) :=
    (smoothOnAlg A Set.univ Set.univ _ _ (1 / 2) hvv hvv subset_rfl).2
  have hΦ' : ∀ i, IsPotential A ((Fin.cons (LocPot.ofFun v) Φ : Fin (e + 1) → LocPot X) i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa using isPotential_ofFun A v hv
    · simpa using hΦ k
  have hΦ2 : ∀ i, IsPotential A
      ((Fin.cons (LocPot.ofFun fun x => 1 / 2 * (v x * v x)) Φ : Fin (e + 1) → LocPot X) i) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa using isPotential_ofFun A _ hv2
    · simpa using hΦ k
  have hsplit : mInt A (Fin.cons (LocPot.ofFun v) Φ) v =
      ∑ m, mInt A (Fin.cons (LocPot.ofFun v) Φ) (fun x => θ m x * v x) := by
    have hv' : v = fun x => ∑ m, θ m x * v x := funext fun x => by rw [← Finset.sum_mul, hθ1, one_mul]
    calc mInt A (Fin.cons (LocPot.ofFun v) Φ) v
        = mInt A (Fin.cons (LocPot.ofFun v) Φ) (fun x => ∑ m, θ m x * v x) := by
          congr 1
      _ = _ := mInt_finset_sum A _ hΦ' (fun m x => θ m x * v x)
          (fun m => (st_smooth_continuous A (hθs m)).mul hvc) Finset.univ
  have hpiece := fun m => st_nonpos_piece A Φ hΦ (j m) (G m) (hGo m) (hGs m) (x0 m) (hGU m) hP v (θ m)
    hv (hθs m) (hθG m)
  have hsum2 : ∑ m, mInt A (Fin.cons (LocPot.ofFun fun x => 1 / 2 * (v x * v x)) Φ) (θ m) = 0 := by
    rw [← mInt_finset_sum A _ hΦ2 θ (fun m => st_smooth_continuous A (hθs m)) Finset.univ]
    have h1 : (fun x => ∑ m, θ m x) = fun _ => 1 := funext hθ1
    rw [h1]
    exact st_stokes_of hP A _ hv2 Φ hΦ
  have hnn : ∀ m, 0 ≤ ∫ y in (A.chart (j m)).target ∩ (A.chart (j m)).symm ⁻¹' G m,
      (A.chart (j m)).target.indicator (θ m ∘ (A.chart (j m)).symm) y *
        gradDens (fun i => (Φ i).φ (x0 m i) ∘ (A.chart (j m)).symm) (v ∘ (A.chart (j m)).symm)
          (v ∘ (A.chart (j m)).symm) y := by
    intro m
    have hUo : IsOpen ((A.chart (j m)).target ∩ (A.chart (j m)).symm ⁻¹' G m) :=
      (A.chart (j m)).isOpen_inter_preimage_symm (hGo m)
    refine setIntegral_nonneg hUo.measurableSet fun y hy => mul_nonneg ?_ ?_
    · exact Set.indicator_nonneg (fun z _ => hθ0 m _) y
    · exact hN e _ _ _ hUo
        (fun i => (((hΦ i).1 (x0 m i) (j m)).mono fun z hz => ⟨hz.1, hGU m i hz.2⟩).of_le h2)
        (fun i z hz ξ => hpsh i (x0 m i) (j m) z ⟨hz.1, hGU m i hz.2⟩ ξ) y hy
  rw [hsplit, Finset.sum_congr rfl fun m _ => hpiece m, Finset.sum_add_distrib, hsum2, add_zero,
    Finset.sum_neg_distrib]
  exact neg_nonpos.mpr (Finset.sum_nonneg fun m _ => hnn m)
end ReciprocityTheory.AnForm.M
