-- Prove2me | solution 1 for TPG.exists_mds_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:59:07.550069+00:00
-- url     : https://prove2.me/submissions/6ac265e0-dd1e-49dd-97b8-3823c4e969cd

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference
import Definitions.Def_TPG_Markov
import Definitions.Def_TPG_Bridge
import Theorems.Thm_TPG_integral_head_mul_tail
import Theorems.Thm_TPG_integral_head_mul_gap_tail
import Theorems.Thm_TPG_mixing_contraction
import Theorems.Thm_TPG_isProbabilityMeasure_trajLaw
import Theorems.Thm_TPG_ae_abs_Y_le

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

/-! ### The balanced randomization probabilities -/

/-- The constant treatment probability `1/2`. -/
private noncomputable def qh : ℕ → ℝ := fun _ => 1 / 2

private lemma hqh : ∀ t : ℕ, 0 ≤ qh t ∧ qh t ≤ 1 := fun _ => by
  unfold qh; constructor <;> norm_num

private lemma qh_shift (r : ℕ) : (fun t => qh (r + t)) = qh := rfl

/-! ### Coordinate functions indexed by natural numbers -/

/-- The inverse-propensity weight of the action at time `s` (zero outside the horizon). -/
private noncomputable def wZ {S : Type} {n : ℕ} (s : ℕ) (ω : Traj S n) : ℝ :=
  if h : s < n then ipw (Z ⟨s, h⟩ ω) else 0

/-- The reward at time `s` clipped to `[-M, M]` (zero outside the horizon). -/
private noncomputable def cY {S : Type} {n : ℕ} (M : ℝ) (s : ℕ) (ω : Traj S n) : ℝ :=
  if h : s < n then max (-M) (min M (Y ⟨s, h⟩ ω)) else 0

/-- The conditional law of the state at time `j + 1` given the state and the action at time `j`
(the zero vector outside the horizon). -/
private noncomputable def pv {S : Type} [Fintype S] (E : Env S) {n : ℕ} (j : ℕ) (ω : Traj S n)
    (a : S) : ℝ :=
  if h : j < n then E.P j (Z ⟨j, h⟩ ω) (X ⟨j, h⟩ ω) a else 0

private lemma abs_ipw_le (z : Bool) : |ipw z| ≤ 2 := by
  unfold ipw
  cases z <;> norm_num

private lemma abs_wZ_le {S : Type} {n : ℕ} (s : ℕ) (ω : Traj S n) : |wZ s ω| ≤ 2 := by
  unfold wZ
  split_ifs
  · exact abs_ipw_le _
  · norm_num

private lemma abs_clip_le (M y : ℝ) : |max (-M) (min M y)| ≤ |M| := by
  rw [abs_le]
  exact ⟨(neg_le_neg (le_abs_self M)).trans (le_max_left _ _),
    max_le (neg_le_abs M) ((min_le_left _ _).trans (le_abs_self M))⟩

private lemma abs_cY_le {S : Type} {n : ℕ} (M : ℝ) (s : ℕ) (ω : Traj S n) : |cY M s ω| ≤ |M| := by
  unfold cY
  split_ifs
  · exact abs_clip_le _ _
  · simp

private lemma abs_wZ_mul_cY_le {S : Type} {n : ℕ} (M : ℝ) (i s : ℕ) (ω : Traj S n) :
    |wZ i ω * cY M s ω| ≤ 2 * |M| := by
  rw [abs_mul]
  exact mul_le_mul (abs_wZ_le _ _) (abs_cY_le _ _ _) (abs_nonneg _) (by norm_num)

/-! #### Behaviour under head and tail maps -/

private lemma wZ_head {S : Type} (m n s : ℕ) (hs : s < m) (ω : Traj S (m + n)) :
    wZ s (headTraj m n ω) = wZ s ω := by
  simp only [wZ, dif_pos hs, dif_pos (show s < m + n by omega)]
  rfl

private lemma wZ_tail {S : Type} (m n s : ℕ) (ω : Traj S (m + n)) :
    wZ s (tailTraj m n ω) = wZ (m + s) ω := by
  by_cases hs : s < n
  · simp only [wZ, dif_pos hs, dif_pos (show m + s < m + n by omega)]
    rfl
  · simp only [wZ, dif_neg hs, dif_neg (show ¬ m + s < m + n by omega)]

private lemma cY_tail {S : Type} (M : ℝ) (m n s : ℕ) (ω : Traj S (m + n)) :
    cY M s (tailTraj m n ω) = cY M (m + s) ω := by
  by_cases hs : s < n
  · simp only [cY, dif_pos hs, dif_pos (show m + s < m + n by omega)]
    rfl
  · simp only [cY, dif_neg hs, dif_neg (show ¬ m + s < m + n by omega)]

private lemma pv_head {S : Type} [Fintype S] (E : Env S) (m n j : ℕ) (hj : j < m)
    (ω : Traj S (m + n)) : pv E j (headTraj m n ω) = pv E j ω := by
  funext a
  simp only [pv, dif_pos hj, dif_pos (show j < m + n by omega)]
  rfl

private lemma pv_last {S : Type} [Fintype S] (E : Env S) (m : ℕ) (ω : Traj S (m + 1)) (a : S) :
    pv E m ω a = E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a := by
  simp only [pv, dif_pos (Nat.lt_succ_self m)]
  rfl

private lemma pv_isProbVec {S : Type} [Fintype S] (E : Env S) {n : ℕ} (j : ℕ) (hj : j < n)
    (ω : Traj S n) : IsProbVec (pv E j ω) := by
  constructor
  · intro a
    simp only [pv, dif_pos hj]
    exact E.P_nonneg _ _ _ _
  · simp only [pv, dif_pos hj]
    exact E.P_row_sum _ _ _

/-! #### Measurability with respect to an arbitrary sigma-algebra on trajectories -/

section meas

variable {S : Type} [MeasurableSpace S]

private lemma wZ_meas_gen {T : ℕ} (m : MeasurableSpace (Traj S T)) (s : ℕ)
    (hs : ∀ h : s < T, Measurable[m] (fun ω : Traj S T => ω ⟨s, h⟩)) :
    Measurable[m] (wZ s : Traj S T → ℝ) := by
  by_cases h : s < T
  · have e : (wZ s : Traj S T → ℝ) = (fun p : S × Bool × ℝ => ipw p.2.1) ∘ fun ω => ω ⟨s, h⟩ := by
      funext ω
      simp only [wZ, dif_pos h, Function.comp]
      rfl
    rw [e]
    exact ((Measurable.of_discrete (f := ipw)).comp (measurable_fst.comp measurable_snd)).comp (hs h)
  · have e : (wZ s : Traj S T → ℝ) = fun _ => 0 := by
      funext ω
      simp only [wZ, dif_neg h]
    rw [e]
    exact measurable_const

private lemma cY_meas_gen {T : ℕ} (m : MeasurableSpace (Traj S T)) (M : ℝ) (s : ℕ)
    (hs : ∀ h : s < T, Measurable[m] (fun ω : Traj S T => ω ⟨s, h⟩)) :
    Measurable[m] (cY M s : Traj S T → ℝ) := by
  by_cases h : s < T
  · have e : (cY M s : Traj S T → ℝ)
        = (fun p : S × Bool × ℝ => max (-M) (min M p.2.2)) ∘ fun ω => ω ⟨s, h⟩ := by
      funext ω
      simp only [cY, dif_pos h, Function.comp]
      rfl
    rw [e]
    exact (measurable_const.max (measurable_const.min (measurable_snd.comp measurable_snd))).comp
      (hs h)
  · have e : (cY M s : Traj S T → ℝ) = fun _ => 0 := by
      funext ω
      simp only [cY, dif_neg h]
    rw [e]
    exact measurable_const

private lemma pv_meas_gen [Fintype S] [MeasurableSingletonClass S] (E : Env S) {T : ℕ}
    (m : MeasurableSpace (Traj S T)) (j : ℕ)
    (hj : ∀ h : j < T, Measurable[m] (fun ω : Traj S T => ω ⟨j, h⟩)) (F : (S → ℝ) → ℝ) :
    Measurable[m] (fun ω : Traj S T => F (pv E j ω)) := by
  by_cases h : j < T
  · have e : (fun ω : Traj S T => F (pv E j ω))
        = (fun p : S × Bool => F (fun a => E.P j p.2 p.1 a))
            ∘ (fun p : S × Bool × ℝ => (p.1, p.2.1)) ∘ fun ω => ω ⟨j, h⟩ := by
      funext ω
      simp only [Function.comp]
      congr 1
      funext a
      simp only [pv, dif_pos h]
      rfl
    rw [e]
    have h1 : Measurable (fun p : S × Bool × ℝ => (p.1, p.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    exact (Measurable.of_discrete (f := fun p : S × Bool => F (fun a => E.P j p.2 p.1 a))).comp
      (h1.comp (hj h))
  · have e : (fun ω : Traj S T => F (pv E j ω)) = fun _ => F (fun _ => 0) := by
      funext ω
      congr 1
      funext a
      simp only [pv, dif_neg h]
    rw [e]
    exact measurable_const

private lemma wZ_meas {T : ℕ} (s : ℕ) : Measurable (wZ s : Traj S T → ℝ) :=
  wZ_meas_gen _ s fun _ => measurable_pi_apply _

private lemma cY_meas {T : ℕ} (M : ℝ) (s : ℕ) : Measurable (cY M s : Traj S T → ℝ) :=
  cY_meas_gen _ M s fun _ => measurable_pi_apply _

private lemma pv_meas [Fintype S] [MeasurableSingletonClass S] (E : Env S) {T : ℕ} (j : ℕ)
    (F : (S → ℝ) → ℝ) : Measurable (fun ω : Traj S T => F (pv E j ω)) :=
  pv_meas_gen E _ j (fun _ => measurable_pi_apply _) F

private lemma head_meas (m n : ℕ) : Measurable (headTraj (S := S) m n) := by
  unfold headTraj
  exact measurable_pi_lambda _ fun i => measurable_pi_apply _

/-! #### The window sigma-algebras -/

private lemma coord_meas_win (T a b s : ℕ) (h : s < T) (ha : a ≤ s) (hb : s ≤ b) :
    Measurable[sigmaWindow T a b] (fun ω : Traj S T => ω ⟨s, h⟩) := by
  refine Measurable.of_comap_le ?_
  exact le_iSup₂ (f := fun (t : Fin T) (_ : a ≤ (t : ℕ) ∧ (t : ℕ) ≤ b) =>
    MeasurableSpace.comap (fun ω : Traj S T => ω t) inferInstance) ⟨s, h⟩ ⟨ha, hb⟩

private lemma win_le (T a b : ℕ) : sigmaWindow (S := S) T a b ≤ MeasurableSpace.pi :=
  iSup₂_le fun t _ => (measurable_pi_apply t).comap_le

private lemma win_mono (T a b b' : ℕ) (hb : b ≤ b') :
    sigmaWindow (S := S) T a b ≤ sigmaWindow T a b' :=
  iSup₂_le fun t ht => le_iSup₂_of_le t ⟨ht.1, ht.2.trans hb⟩ le_rfl

private lemma win_le_comap (m N : ℕ) :
    sigmaWindow (S := S) (m + 1 + N) 0 m
      ≤ MeasurableSpace.comap (headTraj (m + 1) N) MeasurableSpace.pi := by
  refine iSup₂_le fun t ht => ?_
  have ht' : (t : ℕ) < m + 1 := by omega
  have e : (fun ω : Traj S (m + 1 + N) => ω t)
      = (fun ω' : Traj S (m + 1) => ω' ⟨t, ht'⟩) ∘ headTraj (m + 1) N := by
    funext ω
    rfl
  rw [e, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

private lemma win_set (m N : ℕ) (A : Set (Traj S (m + 1 + N)))
    (hA : MeasurableSet[sigmaWindow (m + 1 + N) 0 m] A) :
    ∃ A' : Set (Traj S (m + 1)), MeasurableSet A' ∧ headTraj (m + 1) N ⁻¹' A' = A :=
  MeasurableSpace.measurableSet_comap.1 (win_le_comap m N A hA)

end meas

/-! ### Probability vectors and the mixed kernels -/

section alg

variable {S : Type} [Fintype S]

private lemma abs_dot_le (p g : S → ℝ) (hp : IsProbVec p) (K : ℝ) (hg : ∀ b, |g b| ≤ K) :
    |p ⬝ᵥ g| ≤ K := by
  unfold dotProduct
  calc |∑ b, p b * g b| ≤ ∑ b, |p b * g b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, p b * K := Finset.sum_le_sum fun b _ => by
        rw [abs_mul, abs_of_nonneg (hp.1 b)]
        exact mul_le_mul_of_nonneg_left (hg b) (hp.1 b)
    _ = K := by rw [← Finset.sum_mul, hp.2, one_mul]

private lemma PMix_nonneg (E : Env S) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (s : ℕ) (x y : S) :
    0 ≤ E.PMix θ s x y := by
  simp only [Env.PMix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg h0 (E.P_nonneg _ _ _ _))
    (mul_nonneg (by linarith) (E.P_nonneg _ _ _ _))

private lemma PMix_row_sum (E : Env S) (θ : ℝ) (s : ℕ) (x : S) : ∑ y, E.PMix θ s x y = 1 := by
  simp only [Env.PMix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, E.P_row_sum]
  ring

private lemma isProbVec_vecMul_PMix (E : Env S) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (s : ℕ)
    (v : S → ℝ) (hv : IsProbVec v) : IsProbVec (Matrix.vecMul v (E.PMix θ s)) := by
  constructor
  · intro y
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hv.1 x) (PMix_nonneg E θ h0 h1 s x y)
  · simp only [Matrix.vecMul, dotProduct]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, PMix_row_sum, mul_one]
    exact hv.2

private lemma dot_vecMul_eq (v : S → ℝ) (A : Matrix S S ℝ) (g : S → ℝ) :
    Matrix.vecMul v A ⬝ᵥ g = ∑ a, v a * ∑ b, A a b * g b := by
  rw [← Matrix.dotProduct_mulVec]
  rfl

private lemma P_le_one (E : Env S) (t : ℕ) (z : Bool) (x a : S) : E.P t z x a ≤ 1 := by
  rw [← E.P_row_sum t z x]
  exact Finset.single_le_sum (fun i _ => E.P_nonneg t z x i) (Finset.mem_univ a)

variable [DecidableEq S]

/-- The product of the mixed kernels over the times `a, …, b - 1`. -/
private noncomputable def PiM (E : Env S) (a b : ℕ) : Matrix S S ℝ :=
  ((List.Ico a b).map (fun s => E.PMix (qh s) s)).prod

private lemma PiM_cons (E : Env S) (a b : ℕ) (h : a < b) :
    PiM E a b = E.PMix (qh a) a * PiM E (a + 1) b := by
  unfold PiM
  rw [List.Ico.eq_cons h, List.map_cons, List.prod_cons]

private lemma isProbVec_vecMul_list (E : Env S) (l : List ℕ) (v : S → ℝ) (hv : IsProbVec v) :
    IsProbVec (Matrix.vecMul v ((l.map (fun s => E.PMix (qh s) s)).prod)) := by
  induction l generalizing v with
  | nil => simpa using hv
  | cons s l ih =>
    rw [List.map_cons, List.prod_cons, ← Matrix.vecMul_vecMul]
    exact ih _ (isProbVec_vecMul_PMix E _ (hqh s).1 (hqh s).2 s v hv)

private lemma isProbVec_vecMul_PiM (E : Env S) (a b : ℕ) (v : S → ℝ) (hv : IsProbVec v) :
    IsProbVec (Matrix.vecMul v (PiM E a b)) :=
  isProbVec_vecMul_list E _ v hv

/-- Two probability vectors pushed through the kernels of the times `a, …, b - 1` and tested
against a bounded function differ by at most `2 K γ^(b - a)`. -/
private lemma mix_bound (E : Env S) (γ : ℝ) (hγ0 : 0 ≤ γ) (hmix : ∀ T : ℕ, E.Mixing T γ)
    (a b : ℕ) (hab : a ≤ b) (v u g : S → ℝ) (hv : IsProbVec v) (hu : IsProbVec u) (K : ℝ)
    (hK : 0 ≤ K) (hg : ∀ x, |g x| ≤ K) :
    |Matrix.vecMul v (PiM E a b) ⬝ᵥ g - Matrix.vecMul u (PiM E a b) ⬝ᵥ g|
      ≤ 2 * K * γ ^ (b - a) := by
  rw [← sub_dotProduct, ← Matrix.sub_vecMul]
  have h0 : ∑ x, (v - u) x = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, hv.2, hu.2, sub_self]
  have h1 := mixing_contraction E b γ hγ0 (hmix b) qh hqh a b hab le_rfl (v - u) h0
  have h2 : ∑ x, |(v - u) x| ≤ 2 := by
    calc ∑ x, |(v - u) x| ≤ ∑ x, (v x + u x) := Finset.sum_le_sum fun x _ => by
          rw [Pi.sub_apply]
          exact abs_le.2 ⟨by linarith [hv.1 x, hu.1 x], by linarith [hv.1 x, hu.1 x]⟩
      _ = 2 := by rw [Finset.sum_add_distrib, hv.2, hu.2]; norm_num
  calc |Matrix.vecMul (v - u) (PiM E a b) ⬝ᵥ g|
      ≤ ∑ x, |Matrix.vecMul (v - u) (PiM E a b) x * g x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |Matrix.vecMul (v - u) (PiM E a b) x| * K := Finset.sum_le_sum fun x _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hg x) (abs_nonneg _)
    _ = (∑ x, |Matrix.vecMul (v - u) (PiM E a b) x|) * K := by rw [Finset.sum_mul]
    _ ≤ (γ ^ (b - a) * 2) * K :=
        mul_le_mul_of_nonneg_right
          (h1.trans (mul_le_mul_of_nonneg_left h2 (pow_nonneg hγ0 _))) hK
    _ = 2 * K * γ ^ (b - a) := by ring

end alg

/-! ### Integrals of bounded functions -/

private lemma int_bdd {α : Type} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) : Integrable f ν :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

private lemma abs_int_le {α : Type} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    (f : α → ℝ) (C : ℝ) (hb : ∀ x, |f x| ≤ C) : |∫ x, f x ∂ν| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := ν) (f := f) (C := C)
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  rwa [Real.norm_eq_abs, probReal_univ, mul_one] at h

/-! ### The Markov property as a conditional expectation -/

section markov

variable {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]

private instance trajProb (E : Env S) (T : ℕ) : IsProbabilityMeasure (E.trajLaw T qh) :=
  isProbabilityMeasure_trajLaw E T qh hqh

omit [DecidableEq S] in
private lemma Plast_meas (E : Env S) (m : ℕ) (a : S) :
    Measurable (fun ω : Traj S (m + 1) => E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a) := by
  simpa only [pv_last] using pv_meas E (T := m + 1) m (fun v => v a)

omit [DecidableEq S] in
private lemma int_F_P (E : Env S) (m : ℕ) (F : Traj S (m + 1) → ℝ) (hF : Measurable F) (CF : ℝ)
    (hFb : ∀ ω, |F ω| ≤ CF) (a : S) :
    Integrable (fun ω : Traj S (m + 1) => F ω * E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a)
      (E.trajLaw (m + 1) qh) := by
  refine int_bdd _ _ (hF.mul (Plast_meas E m a)) CF fun ω => ?_
  rw [abs_mul, abs_of_nonneg (E.P_nonneg _ _ _ _)]
  exact (mul_le_of_le_one_right (abs_nonneg _) (P_le_one E _ _ _ _)).trans (hFb ω)

/-- Consistency: a function of the first `m + 1` steps has the same integral under the law of
any longer horizon. -/
private lemma cons_head (E : Env S) (m n : ℕ) (H : Traj S (m + 1) → ℝ) (hH : Measurable H)
    (C : ℝ) (hHb : ∀ ω, |H ω| ≤ C) :
    ∫ ω, H (headTraj (m + 1) n ω) ∂(E.trajLaw (m + 1 + n) qh)
      = ∫ ω, H ω ∂(E.trajLaw (m + 1) qh) := by
  have key := integral_head_mul_tail E m n qh hqh H (fun _ => 1) hH measurable_const C 1 hHb
    (fun _ => by simp)
  simp only [mul_one, qh_shift, integral_const, probReal_univ, one_smul] at key
  rw [key, ← integral_finsetSum _ (fun a _ => int_F_P E m H hH C hHb a)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only []
  rw [← Finset.mul_sum, E.P_row_sum, mul_one]

/-- Integrating the transition row of the last head step against a vector `c` of tail values. -/
private lemma head_pv (E : Env S) (m n : ℕ) (F : Traj S (m + 1) → ℝ) (hF : Measurable F)
    (CF : ℝ) (hFb : ∀ ω, |F ω| ≤ CF) (c : S → ℝ) :
    ∑ a, (∫ ω, F ω * E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a ∂(E.trajLaw (m + 1) qh)) * c a
      = ∫ ω, F (headTraj (m + 1) n ω) * ∑ a, pv E m ω a * c a ∂(E.trajLaw (m + 1 + n) qh) := by
  have hH : Measurable (fun ω : Traj S (m + 1) => F ω * ∑ a, pv E m ω a * c a) :=
    hF.mul (pv_meas E m (fun v => ∑ a, v a * c a))
  have hHb : ∀ ω : Traj S (m + 1), |F ω * ∑ a, pv E m ω a * c a| ≤ |CF| * ∑ a, |c a| := by
    intro ω
    rw [abs_mul]
    refine mul_le_mul ((hFb ω).trans (le_abs_self _)) ?_ (abs_nonneg _) (abs_nonneg _)
    exact abs_dot_le (pv E m ω) c (pv_isProbVec E m (Nat.lt_succ_self m) ω) _
      (fun b => Finset.single_le_sum (fun a _ => abs_nonneg (c a)) (Finset.mem_univ b))
  have h1 := cons_head E m n _ hH _ hHb
  simp only [pv_head E (m + 1) n m (Nat.lt_succ_self m)] at h1
  rw [h1]
  have h2 : ∀ a ∈ (Finset.univ : Finset S), Integrable (fun ω : Traj S (m + 1) =>
      F ω * E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a * c a) (E.trajLaw (m + 1) qh) :=
    fun a _ => (int_F_P E m F hF CF hFb a).mul_const (c a)
  simp only [← integral_mul_const]
  rw [← integral_finsetSum _ h2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [pv_last, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Conditional expectation of a clipped reward after the cut, times an action weight before
the cut. -/
private lemma ce2 (E : Env S) (M : ℝ) (m n i s : ℕ) (hi : i ≤ m) (F : Traj S (m + 1) → ℝ)
    (hF : Measurable F) (CF : ℝ) (hFb : ∀ ω, |F ω| ≤ CF) :
    ∫ ω, F (headTraj (m + 1) n ω) * (wZ i ω * cY M (m + 1 + s) ω) ∂(E.trajLaw (m + 1 + n) qh)
      = ∫ ω, F (headTraj (m + 1) n ω)
          * (wZ i ω * ∑ a, pv E m ω a * ∫ ω', cY M s ω' ∂((E.shift (m + 1) a).trajLaw n qh))
          ∂(E.trajLaw (m + 1 + n) qh) := by
  have hF' : Measurable (fun ω : Traj S (m + 1) => F ω * wZ i ω) := hF.mul (wZ_meas i)
  have hFb' : ∀ ω : Traj S (m + 1), |F ω * wZ i ω| ≤ |CF| * 2 := by
    intro ω
    rw [abs_mul]
    exact mul_le_mul ((hFb ω).trans (le_abs_self _)) (abs_wZ_le _ _) (abs_nonneg _) (abs_nonneg _)
  have key := integral_head_mul_tail E m n qh hqh (fun ω => F ω * wZ i ω) (fun ω => cY M s ω)
    hF' (cY_meas M s) _ |M| hFb' (abs_cY_le M s)
  have hp := head_pv E m n (fun ω => F ω * wZ i ω) hF' _ hFb'
    (fun a => ∫ ω', cY M s ω' ∂((E.shift (m + 1) a).trajLaw n qh))
  simp only [qh_shift, wZ_head (m + 1) n i (by omega), cY_tail] at key hp
  have e1 : ∀ ω : Traj S (m + 1 + n), F (headTraj (m + 1) n ω) * (wZ i ω * cY M (m + 1 + s) ω)
      = F (headTraj (m + 1) n ω) * wZ i ω * cY M (m + 1 + s) ω := fun ω => by ring
  have e2 : ∀ ω : Traj S (m + 1 + n), F (headTraj (m + 1) n ω)
        * (wZ i ω * ∑ a, pv E m ω a * ∫ ω', cY M s ω' ∂((E.shift (m + 1) a).trajLaw n qh))
      = F (headTraj (m + 1) n ω) * wZ i ω
        * ∑ a, pv E m ω a * ∫ ω', cY M s ω' ∂((E.shift (m + 1) a).trajLaw n qh) :=
    fun ω => by ring
  simp only [e1, e2]
  rw [key, hp]

/-- Conditional expectation of a pair term lying entirely after the cut, across a gap. -/
private lemma ce3 (E : Env S) (M : ℝ) (m h n s : ℕ) (F : Traj S (m + 1) → ℝ)
    (hF : Measurable F) (CF : ℝ) (hFb : ∀ ω, |F ω| ≤ CF) :
    ∫ ω, F (headTraj (m + 1) (h + n) ω) * (wZ (m + 1 + h) ω * cY M (m + 1 + h + s) ω)
        ∂(E.trajLaw (m + 1 + (h + n)) qh)
      = ∫ ω, F (headTraj (m + 1) (h + n) ω)
          * (Matrix.vecMul (pv E m ω) (PiM E (m + 1) (m + 1 + h))
              ⬝ᵥ fun b => ∫ ω', wZ 0 ω' * cY M s ω' ∂((E.shift (m + 1 + h) b).trajLaw n qh))
          ∂(E.trajLaw (m + 1 + (h + n)) qh) := by
  have hG : Measurable (fun ω : Traj S n => wZ 0 ω * cY M s ω) := (wZ_meas 0).mul (cY_meas M s)
  have key := integral_head_mul_gap_tail E m h n qh hqh F (fun ω => wZ 0 ω * cY M s ω)
    hF hG CF (2 * |M|) hFb (abs_wZ_mul_cY_le M 0 s)
  have hp := head_pv E m (h + n) F hF CF hFb
    (fun a => ∑ b, PiM E (m + 1) (m + 1 + h) a b
      * ∫ ω', wZ 0 ω' * cY M s ω' ∂((E.shift (m + 1 + h) b).trajLaw n qh))
  have hq' : (fun t => qh (m + 1 + h + t)) = qh := rfl
  simp only [hq', wZ_tail, cY_tail, Nat.add_zero, ← Nat.add_assoc] at key
  simp only [dot_vecMul_eq]
  rw [key, ← hp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_assoc]
  rfl

omit [DecidableEq S] [MeasurableSingletonClass S] in
private lemma setInt_head (E : Env S) (m N : ℕ) (A' : Set (Traj S (m + 1)))
    (hA' : MeasurableSet A') (f : Traj S (m + 1 + N) → ℝ) :
    ∫ ω in headTraj (m + 1) N ⁻¹' A', f ω ∂(E.trajLaw (m + 1 + N) qh)
      = ∫ ω, A'.indicator (fun _ => (1 : ℝ)) (headTraj (m + 1) N ω) * f ω
          ∂(E.trajLaw (m + 1 + N) qh) := by
  rw [← integral_indicator (head_meas (m + 1) N hA')]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  by_cases h : ω ∈ headTraj (m + 1) N ⁻¹' A'
  · rw [Set.indicator_of_mem h]
    show f ω = A'.indicator (fun _ => (1 : ℝ)) (headTraj (m + 1) N ω) * f ω
    rw [Set.indicator_of_mem (Set.mem_preimage.1 h), one_mul]
  · rw [Set.indicator_of_notMem h]
    show (0 : ℝ) = A'.indicator (fun _ => (1 : ℝ)) (headTraj (m + 1) N ω) * f ω
    rw [Set.indicator_of_notMem (fun h' => h (Set.mem_preimage.2 h')), zero_mul]

end markov

/-! ### Sums over the pairs (action time, reward time) -/

/-- Sum over the pairs `(i, t)` with `i ≤ t ≤ i + κ` and `t < T`. -/
private noncomputable def pairSum (κ T : ℕ) (x : ℕ → ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T, ∑ i ∈ Finset.range T, if i ≤ t ∧ t ≤ i + κ then x i t else 0

private lemma pairSum_congr (κ T : ℕ) (x y : ℕ → ℕ → ℝ)
    (h : ∀ i t, i ≤ t → t ≤ i + κ → t < T → x i t = y i t) : pairSum κ T x = pairSum κ T y := by
  unfold pairSum
  refine Finset.sum_congr rfl fun t ht => Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hc
  · exact h i t hc.1 hc.2 (Finset.mem_range.1 ht)
  · rfl

private lemma pairSum_sub (κ T : ℕ) (x y : ℕ → ℕ → ℝ) :
    pairSum κ T x - pairSum κ T y = pairSum κ T (fun i t => x i t - y i t) := by
  unfold pairSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

private lemma pairSum_meas {α : Type} (m : MeasurableSpace α) (κ T : ℕ) (f : ℕ → ℕ → α → ℝ)
    (hf : ∀ i t, i ≤ t → t ≤ i + κ → t < T → Measurable[m] (f i t)) :
    Measurable[m] (fun ω => pairSum κ T (fun i t => f i t ω)) := by
  unfold pairSum
  refine Finset.measurable_sum _ fun t ht => Finset.measurable_sum _ fun i _ => ?_
  by_cases hc : i ≤ t ∧ t ≤ i + κ
  · simp only [if_pos hc]
    exact hf i t hc.1 hc.2 (Finset.mem_range.1 ht)
  · simp only [if_neg hc]
    exact measurable_const

private lemma ite_integrable {α : Type} [MeasurableSpace α] (ν : Measure α) (c : Prop)
    [Decidable c] (f : α → ℝ) (hf : Integrable f ν) :
    Integrable (fun ω => if c then f ω else 0) ν := by
  split_ifs
  · exact hf
  · exact integrable_zero _ _ _

private lemma pairSum_integrable {α : Type} [MeasurableSpace α] (ν : Measure α) (κ T : ℕ)
    (f : ℕ → ℕ → α → ℝ) (hf : ∀ i t, Integrable (f i t) ν) :
    Integrable (fun ω => pairSum κ T (fun i t => f i t ω)) ν := by
  unfold pairSum
  exact integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun i _ =>
    ite_integrable ν _ _ (hf i t)

private lemma pairSum_integral {α : Type} [MeasurableSpace α] (ν : Measure α) (κ T : ℕ)
    (f : ℕ → ℕ → α → ℝ) (hf : ∀ i t, Integrable (f i t) ν) :
    ∫ ω, pairSum κ T (fun i t => f i t ω) ∂ν = pairSum κ T (fun i t => ∫ ω, f i t ω ∂ν) := by
  unfold pairSum
  rw [integral_finsetSum _ (fun t _ => integrable_finsetSum _ fun i _ =>
    ite_integrable ν _ _ (hf i t))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_finsetSum _ (fun i _ => ite_integrable ν _ _ (hf i t))]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rfl
  · simp

private lemma pairSum_abs_le (κ T : ℕ) (x : ℕ → ℕ → ℝ) (b : ℕ → ℝ) (hb : ∀ i, 0 ≤ b i)
    (hx : ∀ i t, i ≤ t → t ≤ i + κ → t < T → |x i t| ≤ b i) :
    |pairSum κ T x| ≤ ((κ : ℝ) + 1) * ∑ i ∈ Finset.range T, b i := by
  unfold pairSum
  rw [Finset.sum_comm, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hcard : ((Finset.range T).filter (fun t => i ≤ t ∧ t ≤ i + κ)).card ≤ κ + 1 := by
    refine (Finset.card_le_card (t := Finset.Icc i (i + κ)) fun t ht => ?_).trans ?_
    · rw [Finset.mem_filter] at ht
      exact Finset.mem_Icc.2 ht.2
    · rw [Nat.card_Icc]
      omega
  calc |∑ t ∈ Finset.range T, if i ≤ t ∧ t ≤ i + κ then x i t else 0|
      ≤ ∑ t ∈ Finset.range T, |if i ≤ t ∧ t ≤ i + κ then x i t else 0| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t ∈ Finset.range T, if i ≤ t ∧ t ≤ i + κ then b i else 0 :=
        Finset.sum_le_sum fun t ht => by
          split_ifs with hc
          · exact hx i t hc.1 hc.2 (Finset.mem_range.1 ht)
          · simp
    _ = ((Finset.range T).filter (fun t => i ≤ t ∧ t ≤ i + κ)).card • b i := by
        rw [← Finset.sum_filter, Finset.sum_const]
    _ ≤ ((κ : ℝ) + 1) * b i := by
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hb i)

private lemma geo_sum (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (T J : ℕ) :
    ∑ i ∈ Finset.range T, (if J < i then γ ^ (i - (J + 1)) else 0) ≤ (1 - γ)⁻¹ := by
  have h : ∀ T : ℕ, ∑ i ∈ Finset.range T, (if J < i then γ ^ (i - (J + 1)) else 0)
      = ∑ d ∈ Finset.range (T - (J + 1)), γ ^ d := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      by_cases hJ : J < T
      · rw [if_pos hJ, show T + 1 - (J + 1) = (T - (J + 1)) + 1 by omega, Finset.sum_range_succ]
      · rw [if_neg hJ, show T + 1 - (J + 1) = T - (J + 1) by omega, add_zero]
  rw [h]
  exact sum_le_hasSum _ (fun _ _ => pow_nonneg hγ0 _) (hasSum_geometric_of_lt_one hγ0 hγ1)

/-- The bound on the difference of two consecutive conditional expectations of a pair term with
action time `i`, at the cut `J`. -/
private noncomputable def betaB (K γ : ℝ) (κ J i : ℕ) : ℝ :=
  if i ≤ J then (if J ≤ i + κ then 2 * K else 0) else 2 * K * γ ^ (i - (J + 1))

private lemma betaB_nonneg (K γ : ℝ) (hK : 0 ≤ K) (hγ0 : 0 ≤ γ) (κ J i : ℕ) :
    0 ≤ betaB K γ κ J i := by
  unfold betaB
  split_ifs <;> positivity

private lemma sum_betaB_le (K γ : ℝ) (hK : 0 ≤ K) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (κ T J : ℕ) :
    ∑ i ∈ Finset.range T, betaB K γ κ J i ≤ 2 * K * ((κ : ℝ) + 1) + 2 * K * (1 - γ)⁻¹ := by
  have h1 : ∀ i, betaB K γ κ J i = (if J ≤ i + κ ∧ i ≤ J then 2 * K else 0)
      + 2 * K * (if J < i then γ ^ (i - (J + 1)) else 0) := by
    intro i
    unfold betaB
    by_cases h : i ≤ J
    · by_cases h' : J ≤ i + κ
      · simp [h, h', not_lt.2 h]
      · simp [h, h', not_lt.2 h]
    · simp [h, not_le.1 h]
  simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  refine add_le_add ?_ (mul_le_mul_of_nonneg_left (geo_sum γ hγ0 hγ1 T J) (by positivity))
  have hcard : ((Finset.range T).filter (fun i => J ≤ i + κ ∧ i ≤ J)).card ≤ κ + 1 := by
    refine (Finset.card_le_card (t := Finset.Icc (J - κ) J) fun i hi => ?_).trans ?_
    · rw [Finset.mem_filter] at hi
      exact Finset.mem_Icc.2 ⟨by omega, hi.2.2⟩
    · rw [Nat.card_Icc]
      omega
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by positivity)

private lemma pairSum_bound (K γ : ℝ) (hK : 0 ≤ K) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (κ T J : ℕ)
    (x : ℕ → ℕ → ℝ) (hx : ∀ i t, i ≤ t → t ≤ i + κ → t < T → |x i t| ≤ betaB K γ κ J i) :
    |pairSum κ T x| ≤ ((κ : ℝ) + 1) * (2 * K * ((κ : ℝ) + 1) + 2 * K * (1 - γ)⁻¹) :=
  (pairSum_abs_le κ T x _ (fun i => betaB_nonneg K γ hK hγ0 κ J i) hx).trans
    (mul_le_mul_of_nonneg_left (sum_betaB_le K γ hK hγ0 hγ1 κ T J) (by positivity))

private lemma abs_sub_le_two (a b K : ℝ) (ha : |a| ≤ K) (hb : |b| ≤ K) : |a - b| ≤ 2 * K := by
  rw [abs_le] at *
  constructor <;> linarith

private lemma abs_ind_le {α : Type} (A : Set α) (x : α) :
    |A.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
  by_cases h : x ∈ A <;> simp [h]

/-! ### Explicit conditional expectations of the pair terms -/

section main

variable {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- Mean clipped reward at time `s` of the environment restarted at time `r` from `a`. -/
private noncomputable def gY (E : Env S) (M : ℝ) (n r s : ℕ) (a : S) : ℝ :=
  ∫ ω, cY M s ω ∂((E.shift r a).trajLaw n qh)

/-- Mean of the pair term (action time `0`, reward time `s`) of the environment restarted at
time `r` from `b`. -/
private noncomputable def gW (E : Env S) (M : ℝ) (n r s : ℕ) (b : S) : ℝ :=
  ∫ ω, wZ 0 ω * cY M s ω ∂((E.shift r b).trajLaw n qh)

private lemma abs_gY_le (E : Env S) (M : ℝ) (n r s : ℕ) (a : S) : |gY E M n r s a| ≤ |M| :=
  abs_int_le _ _ _ (abs_cY_le M s)

private lemma abs_gW_le (E : Env S) (M : ℝ) (n r s : ℕ) (b : S) : |gW E M n r s b| ≤ 2 * |M| :=
  abs_int_le _ _ _ (abs_wZ_mul_cY_le M 0 s)

/-- Explicit version of the conditional expectation of the pair term `w(Z_i) Ỹ_t` given the
first `j + 1` steps of the trajectory. -/
private noncomputable def eP (E : Env S) (M : ℝ) (T i t j : ℕ) (ω : Traj S T) : ℝ :=
  if t ≤ j then wZ i ω * cY M t ω
  else if i ≤ j then wZ i ω * ∑ a, pv E j ω a * gY E M (T - (j + 1)) (j + 1) (t - (j + 1)) a
  else Matrix.vecMul (pv E j ω) (PiM E (j + 1) i) ⬝ᵥ gW E M (T - i) i (t - i)

omit [MeasurableSingletonClass S] in
private lemma eP_one (E : Env S) (M : ℝ) (T i t j : ℕ) (h : t ≤ j) (ω : Traj S T) :
    eP E M T i t j ω = wZ i ω * cY M t ω := by
  simp only [eP, if_pos h]

omit [MeasurableSingletonClass S] in
private lemma eP_two (E : Env S) (M : ℝ) (T i t j : ℕ) (h1 : j < t) (h2 : i ≤ j) (ω : Traj S T) :
    eP E M T i t j ω
      = wZ i ω * ∑ a, pv E j ω a * gY E M (T - (j + 1)) (j + 1) (t - (j + 1)) a := by
  simp only [eP, if_neg (not_le.2 h1), if_pos h2]

omit [MeasurableSingletonClass S] in
private lemma eP_three (E : Env S) (M : ℝ) (T i t j : ℕ) (h2 : j < i) (h1 : i ≤ t)
    (ω : Traj S T) :
    eP E M T i t j ω
      = Matrix.vecMul (pv E j ω) (PiM E (j + 1) i) ⬝ᵥ gW E M (T - i) i (t - i) := by
  simp only [eP, if_neg (not_le.2 (h2.trans_le h1)), if_neg (not_le.2 h2)]

private lemma abs_eP_le (E : Env S) (M : ℝ) (T i t j : ℕ) (hj : j < T) (ω : Traj S T) :
    |eP E M T i t j ω| ≤ 2 * |M| := by
  unfold eP
  split_ifs
  · exact abs_wZ_mul_cY_le M i t ω
  · rw [abs_mul]
    exact mul_le_mul (abs_wZ_le _ _)
      (abs_dot_le (pv E j ω) _ (pv_isProbVec E j hj ω) _ (fun a => abs_gY_le E M _ _ _ a))
      (abs_nonneg _) (by norm_num)
  · exact abs_dot_le _ _ (isProbVec_vecMul_PiM E _ _ _ (pv_isProbVec E j hj ω)) _
      (fun b => abs_gW_le E M _ _ _ b)

private lemma eP_meas_gen (E : Env S) (M : ℝ) (T i t j : ℕ) (m : MeasurableSpace (Traj S T))
    (hj : ∀ h : j < T, Measurable[m] (fun ω : Traj S T => ω ⟨j, h⟩))
    (hi : t ≤ j ∨ i ≤ j → ∀ h : i < T, Measurable[m] (fun ω : Traj S T => ω ⟨i, h⟩))
    (ht : t ≤ j → ∀ h : t < T, Measurable[m] (fun ω : Traj S T => ω ⟨t, h⟩)) :
    Measurable[m] (eP E M T i t j) := by
  by_cases h1 : t ≤ j
  · have e : eP E M T i t j = fun ω => wZ i ω * cY M t ω :=
      funext fun ω => eP_one E M T i t j h1 ω
    rw [e]
    exact (wZ_meas_gen m i (hi (Or.inl h1))).mul (cY_meas_gen m M t (ht h1))
  by_cases h2 : i ≤ j
  · have e : eP E M T i t j = fun ω => wZ i ω
        * ∑ a, pv E j ω a * gY E M (T - (j + 1)) (j + 1) (t - (j + 1)) a :=
      funext fun ω => eP_two E M T i t j (not_le.1 h1) h2 ω
    rw [e]
    exact (wZ_meas_gen m i (hi (Or.inr h2))).mul
      (pv_meas_gen E m j hj (fun v => ∑ a, v a * gY E M (T - (j + 1)) (j + 1) (t - (j + 1)) a))
  · have e : eP E M T i t j = fun ω => Matrix.vecMul (pv E j ω) (PiM E (j + 1) i)
        ⬝ᵥ gW E M (T - i) i (t - i) := by
      funext ω
      simp only [eP, if_neg h1, if_neg h2]
    rw [e]
    exact pv_meas_gen E m j hj
      (fun v => Matrix.vecMul v (PiM E (j + 1) i) ⬝ᵥ gW E M (T - i) i (t - i))

private lemma eP_meas (E : Env S) (M : ℝ) (T i t j : ℕ) : Measurable (eP E M T i t j) :=
  eP_meas_gen E M T i t j _ (fun _ => measurable_pi_apply _) (fun _ _ => measurable_pi_apply _)
    (fun _ _ => measurable_pi_apply _)

private lemma eP_int (E : Env S) (M : ℝ) (T i t j : ℕ) (hj : j < T) :
    Integrable (eP E M T i t j) (E.trajLaw T qh) :=
  int_bdd _ _ (eP_meas E M T i t j) _ (abs_eP_le E M T i t j hj)

omit [DecidableEq S] in
private lemma W_int (E : Env S) (M : ℝ) (T i t : ℕ) :
    Integrable (fun ω : Traj S T => wZ i ω * cY M t ω) (E.trajLaw T qh) :=
  int_bdd _ _ ((wZ_meas i).mul (cY_meas M t)) _ (abs_wZ_mul_cY_le M i t)

/-- The explicit version has the defining property of the conditional expectation. -/
private lemma ce_pair (E : Env S) (M : ℝ) (T i t j : ℕ) (hj : j < T) (hit : i ≤ t) (ht : t < T)
    (A : Set (Traj S T)) (hA : MeasurableSet[sigmaWindow T 0 j] A) :
    ∫ ω in A, eP E M T i t j ω ∂(E.trajLaw T qh)
      = ∫ ω in A, wZ i ω * cY M t ω ∂(E.trajLaw T qh) := by
  by_cases h1 : t ≤ j
  · simp only [eP_one E M T i t j h1]
  by_cases h2 : i ≤ j
  · obtain ⟨n, rfl⟩ : ∃ n, T = j + 1 + n := ⟨T - (j + 1), by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, t = j + 1 + s := ⟨t - (j + 1), by omega⟩
    obtain ⟨A', hA', rfl⟩ := win_set j n A hA
    rw [setInt_head E j n A' hA', setInt_head E j n A' hA']
    simp only [eP_two E M (j + 1 + n) i (j + 1 + s) j (by omega) h2, Nat.add_sub_cancel_left]
    exact (ce2 E M j n i s h2 _ (measurable_const.indicator hA') 1 (abs_ind_le _)).symm
  · obtain ⟨h, rfl⟩ : ∃ h, i = j + 1 + h := ⟨i - (j + 1), by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, t = j + 1 + h + s := ⟨t - (j + 1 + h), by omega⟩
    obtain ⟨n, rfl⟩ : ∃ n, T = j + 1 + (h + n) := ⟨T - (j + 1 + h), by omega⟩
    obtain ⟨A', hA', rfl⟩ := win_set j (h + n) A hA
    rw [setInt_head E j (h + n) A' hA', setInt_head E j (h + n) A' hA']
    have e1 : j + 1 + (h + n) - (j + 1 + h) = n := by omega
    simp only [eP_three E M (j + 1 + (h + n)) (j + 1 + h) (j + 1 + h + s) j (by omega) (by omega),
      e1, Nat.add_sub_cancel_left]
    exact (ce3 E M j h n s _ (measurable_const.indicator hA') 1 (abs_ind_le _)).symm

/-! ### The martingale -/

/-- The sum of the clipped pair terms: almost surely equal to `∑_t B_t`. -/
private noncomputable def Stil (M : ℝ) (κ T : ℕ) (ω : Traj S T) : ℝ :=
  pairSum κ T (fun i t => wZ i ω * cY M t ω)

/-- Explicit version of the conditional expectation of `Stil` given the first `j + 1` steps. -/
private noncomputable def Phi (E : Env S) (M : ℝ) (κ T j : ℕ) (ω : Traj S T) : ℝ :=
  pairSum κ T (fun i t => eP E M T i t j ω)

/-- The martingale indexed by the number of observed steps. -/
private noncomputable def Mart (E : Env S) (M : ℝ) (κ T : ℕ) : ℕ → Traj S T → ℝ
  | 0 => fun _ => ∫ ω', Stil M κ T ω' ∂(E.trajLaw T qh)
  | c + 1 => Phi E M κ T c

/-- The martingale differences. -/
private noncomputable def Dj (E : Env S) (M : ℝ) (κ T j : ℕ) (ω : Traj S T) : ℝ :=
  if j < T then Mart E M κ T (j + 1) ω - Mart E M κ T j ω else 0

private lemma Phi_int (E : Env S) (M : ℝ) (κ T j : ℕ) (hj : j < T) :
    Integrable (Phi E M κ T j) (E.trajLaw T qh) :=
  pairSum_integrable _ κ T (fun i t => eP E M T i t j) (fun i t => eP_int E M T i t j hj)

private lemma ce_Phi (E : Env S) (M : ℝ) (κ T j : ℕ) (hj : j < T) (A : Set (Traj S T))
    (hA : MeasurableSet[sigmaWindow T 0 j] A) :
    ∫ ω in A, Phi E M κ T j ω ∂(E.trajLaw T qh) = ∫ ω in A, Stil M κ T ω ∂(E.trajLaw T qh) := by
  unfold Phi Stil
  rw [pairSum_integral _ κ T (fun i t => eP E M T i t j)
      (fun i t => (eP_int E M T i t j hj).integrableOn),
    pairSum_integral _ κ T (fun i t ω => wZ i ω * cY M t ω)
      (fun i t => (W_int E M T i t).integrableOn)]
  exact pairSum_congr _ _ _ _ fun i t hit _ ht => ce_pair E M T i t j hj hit ht A hA

private lemma int_Phi_zero (E : Env S) (M : ℝ) (κ T : ℕ) (hT : 0 < T) :
    ∫ ω, Phi E M κ T 0 ω ∂(E.trajLaw T qh) = ∫ ω, Stil M κ T ω ∂(E.trajLaw T qh) := by
  have h := ce_Phi E M κ T 0 hT Set.univ MeasurableSet.univ
  rwa [setIntegral_univ, setIntegral_univ] at h

omit [MeasurableSingletonClass S] in
private lemma Mart_last (E : Env S) (M : ℝ) (κ T : ℕ) (ω : Traj S T) :
    Mart E M κ T T ω = Stil M κ T ω := by
  cases T with
  | zero => simp [Mart, Stil, pairSum]
  | succ c =>
    show Phi E M κ (c + 1) c ω = Stil M κ (c + 1) ω
    exact pairSum_congr _ _ _ _ fun i t _ _ ht => eP_one E M _ i t c (by omega) ω

omit [MeasurableSingletonClass S] in
private lemma sum_Dj (E : Env S) (M : ℝ) (κ T : ℕ) (ω : Traj S T) :
    ∑ j ∈ Finset.range T, Dj E M κ T j ω
      = Stil M κ T ω - ∫ ω', Stil M κ T ω' ∂(E.trajLaw T qh) := by
  have h : ∀ j ∈ Finset.range T,
      Dj E M κ T j ω = Mart E M κ T (j + 1) ω - Mart E M κ T j ω := fun j hj => by
    simp only [Dj, if_pos (Finset.mem_range.1 hj)]
  rw [Finset.sum_congr rfl h, Finset.sum_range_sub (fun j => Mart E M κ T j ω), Mart_last]
  rfl

/-! ### Measurability with respect to the window -/

private lemma Dj_meas_win (E : Env S) (M : ℝ) (κ T j : ℕ) :
    Measurable[sigmaWindow T (j - (κ + 1)) j] (Dj E M κ T j) := by
  by_cases hj : j < T
  · have e : Dj E M κ T j = fun ω => Mart E M κ T (j + 1) ω - Mart E M κ T j ω :=
      funext fun ω => by simp only [Dj, if_pos hj]
    rw [e]
    cases j with
    | zero =>
      refine Measurable.sub ?_ measurable_const
      show Measurable[sigmaWindow T (0 - (κ + 1)) 0] (fun ω => Phi E M κ T 0 ω)
      unfold Phi
      refine pairSum_meas _ κ T (fun i t => eP E M T i t 0) fun i t hit htk ht => ?_
      exact eP_meas_gen E M T i t 0 _
        (fun h => coord_meas_win T _ _ 0 h (by omega) le_rfl)
        (fun hh h => coord_meas_win T _ _ i h (by omega) (by omega))
        (fun hh h => coord_meas_win T _ _ t h (by omega) (by omega))
    | succ j' =>
      have e2 : (fun ω => Mart E M κ T (j' + 1 + 1) ω - Mart E M κ T (j' + 1) ω)
          = fun ω => pairSum κ T (fun i t => eP E M T i t (j' + 1) ω - eP E M T i t j' ω) :=
        funext fun ω => pairSum_sub κ T _ _
      rw [e2]
      refine pairSum_meas _ κ T (fun i t ω => eP E M T i t (j' + 1) ω - eP E M T i t j' ω)
        fun i t hit htk ht => ?_
      by_cases h : t ≤ j'
      · have e3 : (fun ω => eP E M T i t (j' + 1) ω - eP E M T i t j' ω) = fun _ => 0 := by
          funext ω
          rw [eP_one E M T i t (j' + 1) (by omega) ω, eP_one E M T i t j' h ω, sub_self]
        rw [e3]
        exact measurable_const
      · refine Measurable.sub ?_ ?_
        · exact eP_meas_gen E M T i t (j' + 1) _
            (fun h' => coord_meas_win T _ _ (j' + 1) h' (by omega) le_rfl)
            (fun hh h' => coord_meas_win T _ _ i h' (by omega) (by omega))
            (fun hh h' => coord_meas_win T _ _ t h' (by omega) (by omega))
        · exact eP_meas_gen E M T i t j' _
            (fun h' => coord_meas_win T _ _ j' h' (by omega) (by omega))
            (fun hh h' => coord_meas_win T _ _ i h' (by omega) (by omega))
            (fun hh h' => coord_meas_win T _ _ t h' (by omega) (by omega))
  · have e : Dj E M κ T j = fun _ => 0 := funext fun ω => by simp only [Dj, if_neg hj]
    rw [e]
    exact measurable_const

/-! ### The uniform bound -/

private lemma eP_mix (E : Env S) (M γ : ℝ) (hγ0 : 0 ≤ γ) (hmix : ∀ T : ℕ, E.Mixing T γ)
    (T i t J : ℕ) (hJ : J < T) (hi : J < i) (hit : i ≤ t) (ω : Traj S T) (u : S → ℝ)
    (hu : IsProbVec u) :
    |eP E M T i t J ω - Matrix.vecMul u (PiM E (J + 1) i) ⬝ᵥ gW E M (T - i) i (t - i)|
      ≤ 2 * (2 * |M|) * γ ^ (i - (J + 1)) := by
  rw [eP_three E M T i t J hi hit ω]
  exact mix_bound E γ hγ0 hmix (J + 1) i hi _ _ _ (pv_isProbVec E J hJ ω) hu _ (by positivity)
    (fun b => abs_gW_le E M _ _ _ b)

private lemma d0_bound (E : Env S) (M γ : ℝ) (hγ0 : 0 ≤ γ) (hmix : ∀ T : ℕ, E.Mixing T γ)
    (κ T : ℕ) (hT : 0 < T) (ω ω' : Traj S T) (i t : ℕ) (hit : i ≤ t) :
    |eP E M T i t 0 ω - eP E M T i t 0 ω'| ≤ betaB (2 * |M|) γ κ 0 i := by
  unfold betaB
  by_cases hi : i ≤ 0
  · rw [if_pos hi, if_pos (Nat.zero_le _)]
    exact abs_sub_le_two _ _ _ (abs_eP_le E M T i t 0 hT ω) (abs_eP_le E M T i t 0 hT ω')
  · rw [if_neg hi, eP_three E M T i t 0 (by omega) hit ω']
    exact eP_mix E M γ hγ0 hmix T i t 0 hT (by omega) hit ω _ (pv_isProbVec E 0 hT ω')

private lemma dj_bound (E : Env S) (M γ : ℝ) (hγ0 : 0 ≤ γ) (hmix : ∀ T : ℕ, E.Mixing T γ)
    (κ T j : ℕ) (hj : j + 1 < T) (ω : Traj S T) (i t : ℕ) (hit : i ≤ t) (htk : t ≤ i + κ) :
    |eP E M T i t (j + 1) ω - eP E M T i t j ω| ≤ betaB (2 * |M|) γ κ (j + 1) i := by
  unfold betaB
  by_cases hi : i ≤ j + 1
  · rw [if_pos hi]
    by_cases hk : j + 1 ≤ i + κ
    · rw [if_pos hk]
      exact abs_sub_le_two _ _ _ (abs_eP_le E M T i t (j + 1) hj ω)
        (abs_eP_le E M T i t j (by omega) ω)
    · rw [if_neg hk, eP_one E M T i t (j + 1) (by omega) ω, eP_one E M T i t j (by omega) ω,
        sub_self, abs_zero]
  · rw [if_neg hi]
    have hi' : j + 1 < i := not_le.1 hi
    rw [eP_three E M T i t j (by omega) hit ω, PiM_cons E (j + 1) i hi', ← Matrix.vecMul_vecMul]
    exact eP_mix E M γ hγ0 hmix T i t (j + 1) hj hi' hit ω _
      (isProbVec_vecMul_PMix E _ (hqh _).1 (hqh _).2 _ _ (pv_isProbVec E j (by omega) ω))

/-- The uniform bound on the martingale differences. -/
private noncomputable def Cc (M γ : ℝ) (κ : ℕ) : ℝ :=
  ((κ : ℝ) + 1) * (2 * (2 * |M|) * ((κ : ℝ) + 1) + 2 * (2 * |M|) * (1 - γ)⁻¹)

private lemma Cc_nonneg (M γ : ℝ) (hγ1 : γ < 1) (κ : ℕ) : 0 ≤ Cc M γ κ := by
  unfold Cc
  have h : 0 ≤ (1 - γ)⁻¹ := inv_nonneg.2 (by linarith)
  positivity

private lemma Dj_bound (E : Env S) (M γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hmix : ∀ T : ℕ, E.Mixing T γ) (κ T j : ℕ) (ω : Traj S T) :
    |Dj E M κ T j ω| ≤ Cc M γ κ := by
  by_cases hj : j < T
  · simp only [Dj, if_pos hj]
    cases j with
    | zero =>
      show |Phi E M κ T 0 ω - ∫ ω', Stil M κ T ω' ∂(E.trajLaw T qh)| ≤ Cc M γ κ
      have h2 : Phi E M κ T 0 ω - ∫ ω', Stil M κ T ω' ∂(E.trajLaw T qh)
          = ∫ ω', (Phi E M κ T 0 ω - Phi E M κ T 0 ω') ∂(E.trajLaw T qh) := by
        rw [integral_sub (integrable_const _) (Phi_int E M κ T 0 hj), integral_const,
          probReal_univ, one_smul, int_Phi_zero E M κ T hj]
      rw [h2]
      refine abs_int_le _ _ _ fun ω' => ?_
      unfold Phi
      rw [pairSum_sub]
      exact pairSum_bound (2 * |M|) γ (by positivity) hγ0 hγ1 κ T 0 _
        fun i t hit _ _ => d0_bound E M γ hγ0 hmix κ T hj ω ω' i t hit
    | succ j' =>
      show |Phi E M κ T (j' + 1) ω - Phi E M κ T j' ω| ≤ Cc M γ κ
      unfold Phi
      rw [pairSum_sub]
      exact pairSum_bound (2 * |M|) γ (by positivity) hγ0 hγ1 κ T (j' + 1) _
        fun i t hit htk _ => dj_bound E M γ hγ0 hmix κ T j' hj ω i t hit htk
  · simp only [Dj, if_neg hj, abs_zero]
    exact Cc_nonneg M γ hγ1 κ

/-! ### The martingale difference property -/

private lemma int_D0 (E : Env S) (M : ℝ) (κ T : ℕ) :
    ∫ ω, Dj E M κ T 0 ω ∂(E.trajLaw T qh) = 0 := by
  by_cases hT : 0 < T
  · simp only [Dj, if_pos hT]
    show ∫ ω, (Phi E M κ T 0 ω - ∫ ω', Stil M κ T ω' ∂(E.trajLaw T qh)) ∂(E.trajLaw T qh) = 0
    rw [integral_sub (Phi_int E M κ T 0 hT) (integrable_const _), integral_const,
      probReal_univ, one_smul, int_Phi_zero E M κ T hT, sub_self]
  · simp only [Dj, if_neg hT, integral_zero]

private lemma condExp_Dj (E : Env S) (M : ℝ) (κ T j : ℕ) :
    (E.trajLaw T qh)[Dj E M κ T (j + 1) | sigmaWindow T 0 j] =ᵐ[E.trajLaw T qh] 0 := by
  by_cases hj : j + 1 < T
  · have e : Dj E M κ T (j + 1) = fun ω => Phi E M κ T (j + 1) ω - Phi E M κ T j ω :=
      funext fun ω => by simp only [Dj, if_pos hj]; rfl
    have hint : Integrable (Dj E M κ T (j + 1)) (E.trajLaw T qh) := by
      rw [e]
      exact (Phi_int E M κ T (j + 1) hj).sub (Phi_int E M κ T j (by omega))
    refine (ae_eq_condExp_of_forall_setIntegral_eq (win_le T 0 j) hint
      (fun s _ _ => integrableOn_zero) (fun s hs _ => ?_) aestronglyMeasurable_zero).symm
    rw [e, integral_sub (Phi_int E M κ T (j + 1) hj).integrableOn
        (Phi_int E M κ T j (by omega)).integrableOn,
      ce_Phi E M κ T (j + 1) hj s (win_mono T 0 j (j + 1) (Nat.le_succ j) s hs),
      ce_Phi E M κ T j (by omega) s hs, sub_self]
    simp
  · have e : Dj E M κ T (j + 1) = 0 := funext fun ω => by simp only [Dj, if_neg hj]; rfl
    rw [e, condExp_zero]

/-! ### The sum of the differences -/

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
private lemma Stil_eq (M : ℝ) (κ T : ℕ) (ω : Traj S T) (h : ∀ t : Fin T, |Y t ω| ≤ M) :
    Stil M κ T ω = ∑ t : Fin T, Bt κ t ω := by
  unfold Stil pairSum Bt
  rw [Finset.sum_range
    (fun t => ∑ i ∈ Finset.range T, if i ≤ t ∧ t ≤ i + κ then wZ i ω * cY M t ω else 0)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_range
    (fun i => if i ≤ (t : ℕ) ∧ (t : ℕ) ≤ i + κ then wZ i ω * cY M (t : ℕ) ω else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : wZ (i : ℕ) ω = ipw (Z i ω) := by
    simp only [wZ, dif_pos i.isLt, Fin.eta]
  have h2 : cY M (t : ℕ) ω = Y t ω := by
    simp only [cY, dif_pos t.isLt, Fin.eta]
    have h3 := abs_le.1 (h t)
    rw [min_eq_right h3.2, max_eq_right h3.1]
  rw [h1, h2]

private lemma ae_sum (E : Env S) (M : ℝ) (hM : E.RewardBound M) (κ T : ℕ) :
    ∀ᵐ ω ∂(E.trajLaw T qh), ∑ j ∈ Finset.range T, Dj E M κ T j ω
      = (∑ t : Fin T, Bt κ t ω) - ∫ ω', ∑ t : Fin T, Bt κ t ω' ∂(E.trajLaw T qh) := by
  have hae : ∀ᵐ ω ∂(E.trajLaw T qh), Stil M κ T ω = ∑ t : Fin T, Bt κ t ω := by
    filter_upwards [ae_abs_Y_le E T qh M hM] with ω hω using Stil_eq M κ T ω hω
  filter_upwards [hae] with ω hω
  rw [sum_Dj, hω, integral_congr_ae hae]

private lemma mds_main (E : Env S) (k : ℕ) (γ M : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hmix : ∀ T : ℕ, E.Mixing T γ) (hM : E.RewardBound M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, ∃ D : ℕ → Traj S T → ℝ,
      (∀ j : ℕ, Measurable[sigmaWindow T (j - (k + 1)) j] (D j))
        ∧ (∀ (j : ℕ) (ω : Traj S T), |D j ω| ≤ C)
        ∧ (∫ ω, D 0 ω ∂(E.expLaw T (1 / 2)) = 0)
        ∧ (∀ j : ℕ, (E.expLaw T (1 / 2))[D (j + 1) | sigmaWindow T 0 j]
              =ᵐ[E.expLaw T (1 / 2)] 0)
        ∧ (∀ᵐ ω ∂(E.expLaw T (1 / 2)),
            ∑ j ∈ Finset.range T, D j ω
              = (∑ t : Fin T, Bt k t ω) - ∫ ω', ∑ t : Fin T, Bt k t ω' ∂(E.expLaw T (1 / 2))) :=
  ⟨Cc M γ k, Cc_nonneg M γ hγ1 k, fun T => ⟨fun j => Dj E M k T j,
    fun j => Dj_meas_win E M k T j,
    fun j ω => Dj_bound E M γ hγ0.le hγ1 hmix k T j ω,
    int_D0 E M k T,
    fun j => condExp_Dj E M k T j,
    ae_sum E M hM k T⟩⟩

end main

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (k : ℕ) (γ M : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hmix : ∀ T : ℕ, E.Mixing T γ) (hM : E.RewardBound M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, ∃ D : ℕ → Traj S T → ℝ,
      (∀ j : ℕ, Measurable[sigmaWindow T (j - (k + 1)) j] (D j))
        ∧ (∀ (j : ℕ) (ω : Traj S T), |D j ω| ≤ C)
        ∧ (∫ ω, D 0 ω ∂(E.expLaw T (1 / 2)) = 0)
        ∧ (∀ j : ℕ, (E.expLaw T (1 / 2))[D (j + 1) | sigmaWindow T 0 j]
              =ᵐ[E.expLaw T (1 / 2)] 0)
        ∧ (∀ᵐ ω ∂(E.expLaw T (1 / 2)),
            ∑ j ∈ Finset.range T, D j ω
              = (∑ t : Fin T, Bt k t ω) - ∫ ω', ∑ t : Fin T, Bt k t ω' ∂(E.expLaw T (1 / 2))) := by
  classical
  exact mds_main E k γ M hγ0 hγ1 hmix hM
