-- Prove2me | solution 1 for TSTutorial.UCBDecomp.ts_prob_matching
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:20:27.018983+00:00
-- url     : https://prove2.me/submissions/46b18040-7c06-4785-8cb9-12fb3bb606df

import Mathlib
import Definitions.Def_TSTutorial_UCBDecomp_Setting

open MeasureTheory
open scoped BigOperators

open TSTutorial.UCBDecomp

variable {X Y Θ : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
  [Fintype Y] [DecidableEq Y] [MeasurableSpace Θ]

private def MB (f : Θ → ℝ) : Prop :=
  Measurable f ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ θ, ‖f θ‖ ≤ C

private lemma mb_const (c : ℝ) : MB (fun _ : Θ => c) :=
  ⟨measurable_const, ‖c‖, norm_nonneg _, fun _ => le_rfl⟩

private lemma mb_add {f g : Θ → ℝ} (hf : MB f) (hg : MB g) :
    MB (fun θ => f θ + g θ) := by
  rcases hf with ⟨hf, C, hC, hfc⟩
  rcases hg with ⟨hg, D, hD, hgd⟩
  exact ⟨hf.add hg, C+D, add_nonneg hC hD,
    fun θ => (norm_add_le _ _).trans (add_le_add (hfc θ) (hgd θ))⟩

private lemma mb_sub {f g : Θ → ℝ} (hf : MB f) (hg : MB g) :
    MB (fun θ => f θ - g θ) := by
  rcases hf with ⟨hf, C, hC, hfc⟩
  rcases hg with ⟨hg, D, hD, hgd⟩
  exact ⟨hf.sub hg, C+D, add_nonneg hC hD,
    fun θ => (norm_sub_le _ _).trans (add_le_add (hfc θ) (hgd θ))⟩

private lemma mb_mul {f g : Θ → ℝ} (hf : MB f) (hg : MB g) :
    MB (fun θ => f θ * g θ) := by
  rcases hf with ⟨hf, C, hC, hfc⟩
  rcases hg with ⟨hg, D, hD, hgd⟩
  refine ⟨hf.mul hg, C*D, mul_nonneg hC hD, fun θ => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hfc θ) (hgd θ) (norm_nonneg _) hC

private lemma mb_sum {I : Type*} (s : Finset I) (f : I → Θ → ℝ)
    (hf : ∀ i ∈ s, MB (f i)) : MB (fun θ => ∑ i ∈ s, f i θ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (mb_const (Θ := Θ) 0)
  | @insert i s hi ih =>
    simpa [Finset.sum_insert hi] using
      mb_add (hf i (by simp)) (ih (fun j hj => hf j (by simp [hj])))

private lemma mb_prod {I : Type*} (s : Finset I) (f : I → Θ → ℝ)
    (hf : ∀ i ∈ s, MB (f i)) : MB (fun θ => ∏ i ∈ s, f i θ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (mb_const (Θ := Θ) 1)
  | @insert i s hi ih =>
    simpa [Finset.prod_insert hi] using
      mb_mul (hf i (by simp)) (ih (fun j hj => hf j (by simp [hj])))

private lemma mb_int (m : Model X Y Θ) {f : Θ → ℝ} (hf : MB f) :
    Integrable f m.prior := by
  letI := m.prior_prob
  rcases hf with ⟨hf, C, _, hb⟩
  exact (integrable_const C).mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hb)

private lemma mb_ite {f g : Θ → ℝ} (p : Θ → Prop) [DecidablePred p]
    (hp : MeasurableSet {θ | p θ}) (hf : MB f) (hg : MB g) :
    MB (fun θ => if p θ then f θ else g θ) := by
  rcases hf with ⟨hf, C, hC, hfc⟩
  rcases hg with ⟨hg, D, hD, hgd⟩
  refine ⟨hf.ite hp hg, C+D, add_nonneg hC hD, fun θ => ?_⟩
  dsimp only
  split_ifs
  · exact (hfc θ).trans (le_add_of_nonneg_right hD)
  · exact (hgd θ).trans (le_add_of_nonneg_left hC)

private lemma mb_select (xStar : Θ → X) (hx : ∀ a, MeasurableSet {θ | xStar θ = a})
    (f : X → Θ → ℝ) (hf : ∀ a, MB (f a)) : MB (fun θ => f (xStar θ) θ) := by
  have hh := mb_sum Finset.univ (fun a θ => if xStar θ = a then f a θ else 0)
    (fun a _ => mb_ite _ (hx a) (hf a) (mb_const 0))
  simpa using hh

private lemma mb_q (m : Model X Y Θ) (a : X) (y : Y) : MB (fun θ => m.q θ a y) := by
  refine ⟨m.q_measurable a y, 1, zero_le_one, fun θ => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (m.q_nonneg θ a y)]
  exact (Finset.single_le_sum (fun z _ => m.q_nonneg θ a z) (Finset.mem_univ y)).trans_eq
    (m.q_sum θ a)

private lemma mb_qlik (m : Model X Y Θ) (s : ℕ) (h : Hist X Y s) :
    MB (fun θ => qlik m s θ h) :=
  mb_prod _ _ (fun i _ => mb_q m (h i).1 (h i).2)

private lemma mb_lik (m : Model X Y Θ) (π : Policy X Y) (s : ℕ) (h : Hist X Y s) :
    MB (fun θ => lik m π s θ h) :=
  mb_prod _ _ (fun i _ => mb_mul (mb_const _) (mb_q m (h i).1 (h i).2))

private lemma mb_mu (m : Model X Y Θ) (a : X) : MB (mu m a) :=
  mb_sum _ _ (fun y _ => mb_mul (mb_q m a y) (mb_const _))

private lemma qlik_nonneg (m : Model X Y Θ) (s : ℕ) (θ : Θ) (h : Hist X Y s) :
    0 ≤ qlik m s θ h :=
  Finset.prod_nonneg (fun i _ => m.q_nonneg θ (h i).1 (h i).2)

private lemma lik_factor (m : Model X Y Θ) (π : Policy X Y) (s : ℕ)
    (θ : Θ) (h : Hist X Y s) :
    lik m π s θ h = (∏ i : Fin s, π i (histPrefix h i) (h i).1) * qlik m s θ h := by
  exact Finset.prod_mul_distrib

private lemma prefix_snoc {s : ℕ} (h : Hist X Y s) (z : X × Y) (i : Fin s) :
    histPrefix (snoc h z) i.castSucc = histPrefix h i := by
  funext j
  change (snoc h z) (Fin.castLE (Nat.le_of_lt i.castSucc.isLt) j) =
    h (Fin.castLE (Nat.le_of_lt i.isLt) j)
  exact Fin.snoc_castSucc (α := fun _ : Fin (s+1) => X × Y) z h
    (Fin.castLE (Nat.le_of_lt i.isLt) j)

private lemma prefix_last {s : ℕ} (h : Hist X Y s) (z : X × Y) :
    histPrefix (snoc h z) (Fin.last s) = h := by
  funext i
  change (snoc h z) i.castSucc = h i
  simp [snoc]

private lemma lik_snoc (m : Model X Y Θ) (π : Policy X Y) (s : ℕ)
    (θ : Θ) (h : Hist X Y s) (a : X) (y : Y) :
    lik m π (s+1) θ (snoc h (a,y)) = lik m π s θ h * π s h a * m.q θ a y := by
  rw [lik, Fin.prod_univ_castSucc]
  simp only [prefix_snoc, prefix_last]
  simp [snoc, lik, mul_assoc]

private lemma marginal (m : Model X Y Θ) (π : Policy X Y) (s : ℕ)
    (h : Hist X Y s) (a : X) :
    (∑ y : Y, histProb m π (s+1) (snoc h (a,y))) = histProb m π s h * π s h a := by
  unfold histProb
  rw [← integral_finsetSum _ (fun y _ => mb_int m (mb_lik m π _ (snoc h (a,y))))]
  simp_rw [lik_snoc]
  simp_rw [← Finset.mul_sum, m.q_sum, mul_one]
  exact integral_mul_const _ _

private lemma matching (m : Model X Y Θ) (xStar : Θ → X)
    (hx : IsOptimalSelector m xStar) (π : Policy X Y)
    (hπ : IsThompsonSampling m xStar π) (s : ℕ) (h : Hist X Y s) (a : X) :
    histProb m π s h * π s h a = jointProb m xStar π s a h := by
  let C : ℝ := ∏ i : Fin s, π i (histPrefix h i) (h i).1
  let e : ℝ := ∫ θ, qlik m s θ h ∂m.prior
  let k : ℝ := ∫ θ, (if xStar θ = a then 1 else 0) * qlik m s θ h ∂m.prior
  have hkmb : MB (fun θ => (if xStar θ = a then 1 else 0) * qlik m s θ h) :=
    mb_mul (mb_ite _ (hx.1 a) (mb_const 1) (mb_const 0)) (mb_qlik m s h)
  have he : 0 ≤ e := integral_nonneg (fun θ => qlik_nonneg m s θ h)
  have hk : 0 ≤ k := integral_nonneg (fun θ => by
    exact mul_nonneg (by split_ifs <;> norm_num) (qlik_nonneg m s θ h))
  have hke : k ≤ e := integral_mono (mb_int m hkmb) (mb_int m (mb_qlik m s h))
    (fun θ => by split_ifs <;> simp_all [qlik_nonneg])
  have hhist : histProb m π s h = C * e := by
    simp only [histProb, lik_factor, integral_const_mul, C, e]
  have hjoint : jointProb m xStar π s a h = C * k := by
    unfold jointProb
    calc
      _ = ∫ θ, C * ((if xStar θ = a then 1 else 0) * qlik m s θ h) ∂m.prior := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun θ => by dsimp only; rw [lik_factor]; dsimp [C]; ring)
      _ = C * k := integral_const_mul _ _
  rw [hhist, hjoint]
  by_cases hepos : 0 < e
  · have hpa : π s h a = k / e := hπ.2 s h hepos a
    rw [hpa]
    field_simp
  · have hez : e = 0 := le_antisymm (le_of_not_gt hepos) he
    have hkz : k = 0 := le_antisymm (by simpa [hez] using hke) hk
    simp [hez, hkz]

theorem solution (m : Model X Y Θ) (xStar : Θ → X)
    (hx : IsOptimalSelector m xStar) (π : Policy X Y)
    (hπ : IsThompsonSampling m xStar π) (s : ℕ)
    (h : Hist X Y s) (a : X) :
    (∑ y : Y, histProb m π (s + 1) (snoc h (a, y))) =
      jointProb m xStar π s a h := by
  rw [marginal]
  exact matching m xStar hx π hπ s h a
