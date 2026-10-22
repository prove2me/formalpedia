-- Prove2me | solution 1 for StochLoadBal.Makespan.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T08:36:50.024134+00:00
-- url     : https://prove2.me/submissions/ea256649-2af5-47ce-a802-8d369c1f86d6

/-
Full exceptional-items lower bound, retaining the platform's explicit independence condition.
Original result: Gupta, Kumar, Nagarajan and Shen (2019), Lemma 1; their proof credits
Kleinberg, Rabani and Tardos for the Bernoulli case. Platform formulation: mikedeng1;
statement review: Shuze Chen. Contribution directed by Alexander Richard Towell (queelius),
with substantial OpenAI Codex proof development and Lean/Mathlib verification assistance.
The all-zero/single-active-event argument proves the general integrable statement.
No claim of mathematical novelty or independent human review is made.
-/
import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Model
open MeasureTheory ProbabilityTheory
namespace ExceptionalLowerBound
noncomputable def z (x : ℝ) : ℝ := if x = 0 then 1 else 0
lemma z_bounds (x : ℝ) : 0 ≤ z x ∧ z x ≤ 1 := by
  unfold z; split_ifs <;> norm_num
lemma z_meas : Measurable z := by
  unfold z
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const measurable_const
lemma z_int {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Measurable f) : Integrable (fun ω => z (f ω)) P := by
  apply (integrable_const (1 : ℝ)).mono' (z_meas.comp hf).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by change ‖z (f ω)‖ ≤ 1; rw [Real.norm_eq_abs, abs_of_nonneg (z_bounds _).1]; exact (z_bounds _).2
end ExceptionalLowerBound
open ExceptionalLowerBound

theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (t : ℕ) (ht : 1 ≤ t) (L : ℝ) (hL : 0 < L) (X : Fin t → Ω → ℝ)
    (hmeas : ∀ j, Measurable (X j)) (hint : ∀ j, Integrable (X j) P)
    (hind : iIndepFun X P)
    (hval : ∀ j ω, X j ω = 0 ∨ L ≤ X j ω)
    (hsum : L ≤ ∑ j, ∫ ω, X j ω ∂P) :
    L / 2 ≤ ∫ ω, (⨆ j, X j ω) ∂P := by
  classical
  let : Nonempty (Fin t) := ⟨⟨0, by omega⟩⟩
  let S : Ω → ℝ := fun ω => ∑ j, X j ω
  let O : Fin t → Ω → ℝ := fun i ω => ∑ j ∈ Finset.univ.erase i, X j ω
  let Z : Ω → ℝ := fun ω => z (S ω)
  let Y : Fin t → Ω → ℝ := fun i ω => z (O i ω)
  let M : Ω → ℝ := fun ω => ⨆ j, X j ω
  have hn (j : Fin t) (ω : Ω) : 0 ≤ X j ω := by rcases hval j ω with h | h; simp [h]; linarith
  have hSm : Measurable S := Finset.measurable_sum _ (fun j _ => hmeas j)
  have hSi : Integrable S P := integrable_finsetSum _ (fun j _ => hint j)
  have hOm (j : Fin t) : Measurable (O j) := Finset.measurable_sum _ (fun j _ => hmeas j)
  have hZi : Integrable Z P := z_int P S hSm
  have hYi (j : Fin t) : Integrable (Y j) P := z_int P (O j) (hOm j)
  have hXYi (j : Fin t) : Integrable (fun ω => X j ω * Y j ω) P :=
    (hint j).mul_bdd (z_meas.comp (hOm j)).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      change ‖z (O j ω)‖ ≤ (1:ℝ); rw [Real.norm_eq_abs, abs_of_nonneg (z_bounds _).1]; exact (z_bounds _).2)
  have hMge (j : Fin t) (ω : Ω) : X j ω ≤ M ω := le_ciSup (Finite.bddAbove_range (fun k => X k ω)) j
  have hMn (ω : Ω) : 0 ≤ M ω := (hn ⟨0, by omega⟩ ω).trans (hMge _ _)
  have hMi : Integrable M P := by
    apply hSi.mono' (Measurable.iSup hmeas).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hMn ω)]
    exact ciSup_le fun j => Finset.single_le_sum (fun k _ => hn k ω) (Finset.mem_univ j)
  have hOzero (ω : Ω) (h : S ω = 0) (i : Fin t) : O i ω = 0 := by
    have hall : ∀ j, X j ω = 0 := by
      have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => hn j ω)).1 h
      exact fun j => hh j (Finset.mem_univ j)
    simp [O, hall]
  have hZY (j : Fin t) (ω : Ω) : Z ω ≤ Y j ω := by
    by_cases h : S ω = 0
    · simp [Z, Y, z, h, hOzero ω h j]
    · simpa [Z, Y, z, h] using (z_bounds (O j ω)).1
  have hfactor (j : Fin t) : (∫ ω, X j ω * Y j ω ∂P) = (∫ ω, X j ω ∂P) * (∫ ω, Y j ω ∂P) := by
    have hh := (hind.indepFun_finsetSum_of_notMem hmeas (Finset.notMem_erase j Finset.univ)).symm
    have hi : IndepFun (X j) (Y j) P := by
      simpa only [Function.comp_def, id_eq, Finset.sum_apply, O, Y] using hh.comp measurable_id z_meas
    exact hi.integral_fun_mul_eq_mul_integral (hint j).aestronglyMeasurable (hYi j).aestronglyMeasurable
  have hpoint (ω : Ω) : (∑ j, X j ω * Y j ω) ≤ M ω := by
    by_cases he : ∃ k, X k ω ≠ 0
    · obtain ⟨k, hk⟩ := he
      have hrest (j : Fin t) (hj : j ≠ k) : X j ω * Y j ω = 0 := by
        have hp : 0 < X k ω := lt_of_le_of_ne (hn k ω) (Ne.symm hk)
        have hb : X k ω ≤ O j ω := Finset.single_le_sum (fun i _ => hn i ω) (by simp [hj.symm])
        have ho : O j ω ≠ 0 := ne_of_gt (hp.trans_le hb)
        simp [Y, z, ho]
      rw [Finset.sum_eq_single k (fun j _ hj => hrest j hj) (by simp)]
      exact (mul_le_of_le_one_right (hn k ω) (z_bounds _).2).trans (hMge k ω)
    · have hz : ∀ k, X k ω = 0 := by simpa using he
      simpa [hz] using hMn ω
  have hbound1 : L * (1 - ∫ ω, Z ω ∂P) ≤ ∫ ω, M ω ∂P := by
    have hpoint1 (ω : Ω) : L * (1 - Z ω) ≤ M ω := by
      by_cases h : S ω = 0
      · simpa [Z, z, h] using hMn ω
      · have he : ∃ j, X j ω ≠ 0 := by
          by_contra! hh
          exact h (by simp [S, hh])
        obtain ⟨j, hj⟩ := he
        have hLj : L ≤ X j ω := (hval j ω).resolve_left hj
        simpa [Z, z, h] using hLj.trans (hMge j ω)
    have hi := integral_mono ((integrable_const (1:ℝ)).sub hZi |>.const_mul L) hMi hpoint1
    change (∫ ω, L * (1 - Z ω) ∂P) ≤ ∫ ω, M ω ∂P at hi
    simpa only [integral_const_mul, integral_sub (integrable_const (1:ℝ)) hZi, integral_const,
      probReal_univ, smul_eq_mul, one_mul] using hi
  have hbound2 : (∑ j, ∫ ω, X j ω ∂P) * (∫ ω, Z ω ∂P) ≤ ∫ ω, M ω ∂P := by
    calc
      _ = ∑ j, (∫ ω, X j ω ∂P) * (∫ ω, Z ω ∂P) := Finset.sum_mul _ _ _
      _ ≤ ∑ j, (∫ ω, X j ω ∂P) * (∫ ω, Y j ω ∂P) := Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (integral_mono hZi (hYi j) (hZY j)) (integral_nonneg (hn j)))
      _ = ∫ ω, ∑ j, X j ω * Y j ω ∂P := by rw [integral_finsetSum _ (fun j _ => hXYi j)]; simp only [hfactor]
      _ ≤ _ := integral_mono (integrable_finsetSum _ (fun j _ => hXYi j)) hMi hpoint
  by_cases hq : (∫ ω, Z ω ∂P) ≤ 1/2
  · nlinarith
  · have hp : 0 ≤ ∫ ω, Z ω ∂P := integral_nonneg (fun ω => (z_bounds (S ω)).1)
    have hh := mul_le_mul_of_nonneg_right hsum hp
    nlinarith
#print axioms solution
