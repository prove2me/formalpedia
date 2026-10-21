-- Prove2me | solution 1 for TSTutorial.InfoRatio.regret_le_sqrt_infoRatio_entropy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T04:58:29.873549+00:00
-- url     : https://prove2.me/submissions/d75156a6-3511-4ede-8ab1-2565d05d6386

import Mathlib
import Definitions.Def_TSTutorial_InfoRatio_Setting

set_option autoImplicit false

open MeasureTheory

namespace TSTutorial.InfoRatio.Aux

open TSTutorial.InfoRatio

variable {X Y Θ : Type} [Fintype X] [DecidableEq X] [Fintype Y] [MeasurableSpace Θ]

lemma histPrefix_snoc {t s : ℕ} (h : Hist X Y t) (z : X × Y) (hs : s ≤ t) (hs' : s ≤ t + 1) :
    histPrefix (Fin.snoc (α := fun _ => X × Y) h z) s hs' = histPrefix h s hs := by
  funext j
  simp only [histPrefix]
  have e : (Fin.castLE hs' j : Fin (t + 1)) = Fin.castSucc (Fin.castLE hs j) := by
    ext; simp
  rw [e, Fin.snoc_castSucc]

lemma histPrefix_self {t : ℕ} (h : Hist X Y t) : histPrefix h t le_rfl = h := by
  funext j
  simp only [histPrefix]
  congr 1

lemma lik_snoc (M : Model X Y Θ) (π : Policy X Y) {t : ℕ} (θ : Θ) (h : Hist X Y t)
    (z : X × Y) :
    lik M π (t + 1) θ (Fin.snoc (α := fun _ => X × Y) h z)
      = lik M π t θ h * (π t h z.1 * M.q θ z.1 z.2) := by
  unfold lik
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    have e1 : (Fin.snoc (α := fun _ => X × Y) h z) (Fin.castSucc i) = h i :=
      Fin.snoc_castSucc (α := fun _ => X × Y) ..
    rw [e1]
    show π i.val (histPrefix (Fin.snoc (α := fun _ => X × Y) h z) i.val _) (h i).1
        * M.q θ (h i).1 (h i).2 = _
    rw [histPrefix_snoc h z i.isLt.le]
  · show π t (histPrefix (Fin.snoc (α := fun _ => X × Y) h z) t _)
        ((Fin.snoc (α := fun _ => X × Y) h z) (Fin.last t)).1
        * M.q θ ((Fin.snoc (α := fun _ => X × Y) h z) (Fin.last t)).1
          ((Fin.snoc (α := fun _ => X × Y) h z) (Fin.last t)).2 = _
    rw [histPrefix_snoc h z le_rfl, histPrefix_self, Fin.snoc_last]

lemma pi_le_one {π : Policy X Y} (hπ : IsPolicy π) (t : ℕ) (h : Hist X Y t) (a : X) :
    π t h a ≤ 1 := by
  rw [← hπ.2 t h]
  exact Finset.single_le_sum (fun b _ => hπ.1 t h b) (Finset.mem_univ a)

lemma q_le_one (M : Model X Y Θ) (θ : Θ) (x : X) (y : Y) : M.q θ x y ≤ 1 := by
  rw [← M.q_sum_one θ x]
  exact Finset.single_le_sum (fun b _ => M.q_nonneg θ x b) (Finset.mem_univ y)

lemma lik_nonneg (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) (t : ℕ) (θ : Θ)
    (h : Hist X Y t) : 0 ≤ lik M π t θ h :=
  Finset.prod_nonneg fun s _ => mul_nonneg (hπ.1 _ _ _) (M.q_nonneg _ _ _)

lemma lik_le_one (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) (t : ℕ) (θ : Θ)
    (h : Hist X Y t) : lik M π t θ h ≤ 1 :=
  Finset.prod_le_one (fun s _ => mul_nonneg (hπ.1 _ _ _) (M.q_nonneg _ _ _))
    (fun s _ => mul_le_one₀ (pi_le_one hπ _ _ _) (M.q_nonneg _ _ _) (q_le_one M _ _ _))

lemma lik_meas (M : Model X Y Θ) (π : Policy X Y) (t : ℕ) (h : Hist X Y t) :
    Measurable (fun θ => lik M π t θ h) := by
  unfold lik
  exact Finset.measurable_prod _ (fun s _ => (M.q_measurable _ _).const_mul _)

lemma ind_meas (M : Model X Y Θ) (a : X) :
    Measurable (fun θ => if M.xStar θ = a then (1 : ℝ) else 0) :=
  Measurable.ite (M.xStar_measurable a) measurable_const measurable_const

lemma lik_int (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) (t : ℕ)
    (h : Hist X Y t) : Integrable (fun θ => lik M π t θ h) M.P := by
  haveI := M.P_prob
  refine Integrable.of_bound (lik_meas M π t h).aestronglyMeasurable 1
    (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (lik_nonneg M hπ t θ h)]
  exact lik_le_one M hπ t θ h

lemma indlik_int (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) (t : ℕ) (a : X)
    (h : Hist X Y t) :
    Integrable (fun θ => (if M.xStar θ = a then (1 : ℝ) else 0) * lik M π t θ h) M.P := by
  haveI := M.P_prob
  refine Integrable.of_bound ((ind_meas M a).mul (lik_meas M π t h)).aestronglyMeasurable 1
    (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs]
  have h0 := lik_nonneg M hπ t θ h
  have h1 := lik_le_one M hπ t θ h
  split_ifs
  · rw [one_mul, abs_of_nonneg h0]; exact h1
  · simp

lemma sum_step (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) {t : ℕ} (θ : Θ)
    (h : Hist X Y t) :
    ∑ z : X × Y, lik M π (t + 1) θ (Fin.snoc (α := fun _ => X × Y) h z) = lik M π t θ h := by
  simp_rw [lik_snoc]
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, M.q_sum_one, mul_one, hπ.2, mul_one]

lemma sum_snoc {t : ℕ} (F : Hist X Y (t + 1) → ℝ) :
    ∑ h, F h = ∑ h : Hist X Y t, ∑ z : X × Y, F (Fin.snoc (α := fun _ => X × Y) h z) := by
  rw [← (Fin.snocEquiv (fun _ => X × Y)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

lemma J_snoc_sum (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) {t : ℕ} (a : X)
    (h : Hist X Y t) :
    ∑ z : X × Y, jointProb M π (t + 1) a (Fin.snoc (α := fun _ => X × Y) h z)
      = jointProb M π t a h := by
  unfold jointProb
  rw [← integral_finsetSum _ (fun z _ => indlik_int M hπ (t + 1) a _)]
  congr 1
  funext θ
  rw [← Finset.mul_sum, sum_step M hπ θ h]

lemma P_eq_sum_J (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) (t : ℕ)
    (h : Hist X Y t) : histProb M π t h = ∑ a, jointProb M π t a h := by
  unfold histProb jointProb
  rw [← integral_finsetSum _ (fun a _ => indlik_int M hπ t a h)]
  congr 1
  funext θ
  rw [← Finset.sum_mul]
  simp [Finset.sum_ite_eq]

lemma J_nonneg (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) (t : ℕ) (a : X)
    (h : Hist X Y t) : 0 ≤ jointProb M π t a h := by
  unfold jointProb
  refine integral_nonneg fun θ => mul_nonneg ?_ (lik_nonneg M hπ t θ h)
  split_ifs <;> norm_num

lemma J_le_P (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) (t : ℕ) (a : X)
    (h : Hist X Y t) : jointProb M π t a h ≤ histProb M π t h := by
  rw [P_eq_sum_J M hπ]
  exact Finset.single_le_sum (fun b _ => J_nonneg M hπ t b h) (Finset.mem_univ a)

lemma J_le_prev (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) {t : ℕ} (a : X)
    (h : Hist X Y t) (z : X × Y) :
    jointProb M π (t + 1) a (Fin.snoc (α := fun _ => X × Y) h z) ≤ jointProb M π t a h := by
  rw [← J_snoc_sum M hπ a h]
  exact Finset.single_le_sum (f := fun z => jointProb M π (t + 1) a
    (Fin.snoc (α := fun _ => X × Y) h z)) (fun b _ => J_nonneg M hπ _ _ _) (Finset.mem_univ z)

/-- minus the conditional entropy of `x*` given `ℍ_t` -/
noncomputable def phi (M : Model X Y Θ) (π : Policy X Y) (t : ℕ) : ℝ :=
  ∑ h : Hist X Y t, ∑ a, jointProb M π t a h *
    (Real.log (jointProb M π t a h) - Real.log (histProb M π t h))

lemma cmi_eq (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) (s : ℕ) :
    condMutualInfo M π s = phi M π (s + 1) - phi M π s := by
  have key : ∀ (h : Hist X Y s) (a : X) (z : X × Y),
      jointProb M π (s + 1) a (Fin.snoc (α := fun _ => X × Y) h z) *
        Real.log (jointProb M π (s + 1) a (Fin.snoc (α := fun _ => X × Y) h z)
          * histProb M π s h / (jointProb M π s a h
            * histProb M π (s + 1) (Fin.snoc (α := fun _ => X × Y) h z)))
      = jointProb M π (s + 1) a (Fin.snoc (α := fun _ => X × Y) h z) *
          (Real.log (jointProb M π (s + 1) a (Fin.snoc (α := fun _ => X × Y) h z))
            - Real.log (histProb M π (s + 1) (Fin.snoc (α := fun _ => X × Y) h z)))
        - jointProb M π (s + 1) a (Fin.snoc (α := fun _ => X × Y) h z) *
          (Real.log (jointProb M π s a h) - Real.log (histProb M π s h)) := by
    intro h a z
    set Jz := jointProb M π (s + 1) a (Fin.snoc (α := fun _ => X × Y) h z) with hJz
    by_cases hz : Jz = 0
    · simp [hz]
    have pos : 0 < Jz := lt_of_le_of_ne (J_nonneg M hπ _ _ _) (Ne.symm hz)
    have hJa : 0 < jointProb M π s a h := lt_of_lt_of_le pos (J_le_prev M hπ a h z)
    have hPh : 0 < histProb M π s h := lt_of_lt_of_le hJa (J_le_P M hπ s a h)
    have hPz : 0 < histProb M π (s + 1) (Fin.snoc (α := fun _ => X × Y) h z) :=
      lt_of_lt_of_le pos (J_le_P M hπ _ a _)
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul pos.ne' hPh.ne',
      Real.log_mul hJa.ne' hPz.ne']
    ring
  unfold condMutualInfo
  simp_rw [key, Finset.sum_sub_distrib]
  unfold phi
  congr 1
  · rw [sum_snoc (fun h' => ∑ a, jointProb M π (s + 1) a h' *
      (Real.log (jointProb M π (s + 1) a h') - Real.log (histProb M π (s + 1) h')))]
    exact Finset.sum_congr rfl fun h _ => Finset.sum_comm
  · refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_mul, J_snoc_sum M hπ a h]

lemma P_zero (M : Model X Y Θ) (π : Policy X Y) (h : Hist X Y 0) : histProb M π 0 h = 1 := by
  haveI := M.P_prob
  simp [histProb, lik]

lemma J_zero (M : Model X Y Θ) (π : Policy X Y) (a : X) (h : Hist X Y 0) :
    jointProb M π 0 a h = starProb M a := by
  have e : (fun θ => (if M.xStar θ = a then (1 : ℝ) else 0) * lik M π 0 θ h)
      = (M.xStar ⁻¹' {a}).indicator 1 := by
    funext θ
    by_cases hx : M.xStar θ = a <;> simp [lik, Set.indicator, hx]
  unfold jointProb starProb
  rw [e, integral_indicator_one (M.xStar_measurable a), measureReal_def]

lemma phi_zero (M : Model X Y Θ) (π : Policy X Y) : phi M π 0 = - entropyStar M := by
  unfold phi entropyStar
  simp only [P_zero, J_zero, Real.log_one, sub_zero, Finset.univ_unique, Finset.sum_singleton]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Real.negMulLog]

lemma phi_nonpos (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) (t : ℕ) :
    phi M π t ≤ 0 := by
  unfold phi
  refine Finset.sum_nonpos fun h _ => Finset.sum_nonpos fun a _ => ?_
  by_cases hz : jointProb M π t a h = 0
  · simp [hz]
  have pos : 0 < jointProb M π t a h := lt_of_le_of_ne (J_nonneg M hπ _ _ _) (Ne.symm hz)
  have hle := J_le_P M hπ t a h
  have : Real.log (jointProb M π t a h) ≤ Real.log (histProb M π t h) :=
    Real.log_le_log pos hle
  nlinarith

lemma sum_cmi_le (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) (T : ℕ) :
    ∑ s : Fin T, condMutualInfo M π s ≤ entropyStar M := by
  simp_rw [cmi_eq M hπ]
  rw [Fin.sum_univ_eq_sum_range (fun s => phi M π (s + 1) - phi M π s) T,
    Finset.sum_range_sub, phi_zero]
  have := phi_nonpos M hπ T
  linarith

lemma mu_abs_le (M : Model X Y Θ) (x : X) (θ : Θ) :
    |mu M.q M.r x θ| ≤ ∑ y, |M.r y| := by
  unfold mu
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [abs_mul, abs_of_nonneg (M.q_nonneg θ x y)]
  exact mul_le_of_le_one_left (abs_nonneg _) (q_le_one M θ x y)

lemma mu_meas (M : Model X Y Θ) (x : X) : Measurable (fun θ => mu M.q M.r x θ) := by
  unfold mu
  exact Finset.measurable_sum _ fun y _ => (M.q_measurable x y).mul_const _

lemma muStar_meas (M : Model X Y Θ) : Measurable (fun θ => mu M.q M.r (M.xStar θ) θ) := by
  have e : (fun θ => mu M.q M.r (M.xStar θ) θ)
      = fun θ => ∑ a, (if M.xStar θ = a then mu M.q M.r a θ else 0) := by
    funext θ
    simp [Finset.sum_ite_eq]
  rw [e]
  exact Finset.measurable_sum _ fun a _ =>
    Measurable.ite (M.xStar_measurable a) (mu_meas M a) measurable_const

lemma regret_decomp (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) (θ : Θ) (T : ℕ) :
    ∑ h : Hist X Y T, lik M π T θ h *
        ∑ s : Fin T, (mu M.q M.r (M.xStar θ) θ - mu M.q M.r (h s).1 θ)
      = ∑ s : Fin T, ∑ h : Hist X Y (s + 1), lik M π (s + 1) θ h *
          (mu M.q M.r (M.xStar θ) θ - mu M.q M.r (h (Fin.last s)).1 θ) := by
  induction T with
  | zero => simp
  | succ t ih =>
    rw [Fin.sum_univ_castSucc (f := fun s : Fin (t + 1) =>
      ∑ h : Hist X Y (s + 1), lik M π (s + 1) θ h *
          (mu M.q M.r (M.xStar θ) θ - mu M.q M.r (h (Fin.last s)).1 θ))]
    show _ = ∑ s : Fin t, (∑ h : Hist X Y (s + 1), lik M π (s + 1) θ h *
          (mu M.q M.r (M.xStar θ) θ - mu M.q M.r (h (Fin.last s)).1 θ))
        + ∑ h : Hist X Y (t + 1), lik M π (t + 1) θ h * (mu M.q M.r (M.xStar θ) θ - mu M.q M.r (h (Fin.last t)).1 θ)
    rw [sum_snoc (fun h' : Hist X Y (t + 1) => lik M π (t + 1) θ h' *
          ∑ s : Fin (t + 1), (mu M.q M.r (M.xStar θ) θ - mu M.q M.r (h' s).1 θ)),
        sum_snoc (fun h' : Hist X Y (t + 1) => lik M π (t + 1) θ h' * (mu M.q M.r (M.xStar θ) θ - mu M.q M.r (h' (Fin.last t)).1 θ)),
        ← ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun h _ => ?_
    simp only [Fin.sum_univ_castSucc (n := t), Fin.snoc_castSucc, Fin.snoc_last, mul_add,
      Finset.sum_add_distrib]
    congr 1
    rw [← Finset.sum_mul, sum_step M hπ θ h]

lemma F_int (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) (s : ℕ) :
    Integrable (fun θ => ∑ h : Hist X Y (s + 1), lik M π (s + 1) θ h *
      (mu M.q M.r (M.xStar θ) θ - mu M.q M.r (h (Fin.last s)).1 θ)) M.P := by
  haveI := M.P_prob
  refine integrable_finset_sum _ fun h _ => ?_
  refine Integrable.of_bound (((lik_meas M π _ h).mul ((muStar_meas M).sub
    (mu_meas M _))).aestronglyMeasurable) (2 * ∑ y, |M.r y|) (ae_of_all _ fun θ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (lik_nonneg M hπ _ θ h)]
  have h1 := lik_le_one M hπ _ θ h
  have h0 := lik_nonneg M hπ _ θ h
  have hg : |mu M.q M.r (M.xStar θ) θ - mu M.q M.r (h (Fin.last s)).1 θ| ≤ 2 * ∑ y, |M.r y| := by
    refine (abs_sub _ _).trans ?_
    have := mu_abs_le M (M.xStar θ) θ
    have := mu_abs_le M (h (Fin.last s)).1 θ
    linarith
  calc lik M π (s + 1) θ h * |mu M.q M.r (M.xStar θ) θ - mu M.q M.r (h (Fin.last s)).1 θ|
      ≤ 1 * (2 * ∑ y, |M.r y|) := mul_le_mul h1 hg (abs_nonneg _) zero_le_one
    _ = 2 * ∑ y, |M.r y| := one_mul _

lemma expRegret_eq (M : Model X Y Θ) {π : Policy X Y} (hπ : IsPolicy π) (T : ℕ) :
    expRegret M π T = ∑ s : Fin T, periodRegret M π s := by
  unfold expRegret periodRegret
  simp_rw [regret_decomp M hπ _ T]
  exact integral_finsetSum _ fun s _ => F_int M hπ s

end TSTutorial.InfoRatio.Aux

open TSTutorial.InfoRatio.Aux in
open TSTutorial.InfoRatio in
theorem solution {X Y Θ : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [MeasurableSpace Θ] (M : Model X Y Θ) (π : Policy X Y) (hπ : IsPolicy π) (T : ℕ)
    (Γ : ℝ) (hΓ_nonneg : 0 ≤ Γ)
    (hΓ : ∀ s : Fin T, periodRegret M π s ^ 2 ≤ Γ * condMutualInfo M π s) :
    expRegret M π T ≤ Real.sqrt (Γ * entropyStar M * T) := by
  rw [expRegret_eq M hπ T]
  have hI := sum_cmi_le M hπ T
  have hnn : ∀ s : Fin T, 0 ≤ Γ * condMutualInfo M π s := fun s =>
    (sq_nonneg _).trans (hΓ s)
  have hb : ∀ s : Fin T, periodRegret M π s ≤ Real.sqrt (Γ * condMutualInfo M π s) :=
    fun s => (le_abs_self _).trans (Real.abs_le_sqrt (hΓ s))
  have hsum : ∑ s : Fin T, periodRegret M π s
      ≤ ∑ s : Fin T, Real.sqrt (Γ * condMutualInfo M π s) := Finset.sum_le_sum fun s _ => hb s
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin T)))
    (f := fun s => Real.sqrt (Γ * condMutualInfo M π s))
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  have hsq : ∀ s : Fin T, Real.sqrt (Γ * condMutualInfo M π s) ^ 2
      = Γ * condMutualInfo M π s := fun s => Real.sq_sqrt (hnn s)
  simp_rw [hsq] at hcs
  rw [← Finset.mul_sum] at hcs
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have h2 : (∑ s : Fin T, Real.sqrt (Γ * condMutualInfo M π s)) ^ 2
      ≤ Γ * entropyStar M * T := by
    calc _ ≤ (T : ℝ) * (Γ * ∑ s : Fin T, condMutualInfo M π s) := hcs
      _ ≤ (T : ℝ) * (Γ * entropyStar M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hI hΓ_nonneg) hT
      _ = Γ * entropyStar M * T := by ring
  exact hsum.trans ((le_abs_self _).trans (Real.abs_le_sqrt h2))
