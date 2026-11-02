-- Prove2me | solution 1 for SeqMechExPost.Optimal.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:54:18.860305+00:00
-- url     : https://prove2.me/submissions/5af4d109-83b6-44c7-89aa-3b4fc86cdef3

import Mathlib
import Definitions.Def_SeqMechExPost_Optimal_Model
import Definitions.Def_SeqMechExPost_Optimal_Tradeoff


open MeasureTheory

namespace SeqMechExPost.Optimal.SMAux

open SeqMechExPost.Optimal

variable {k : ℕ}

instance law_isProb (I : Instance k) : IsProbabilityMeasure I.law := by
  unfold Instance.law; infer_instance

lemma ae_box (I : Instance k) : ∀ᵐ w ∂I.law, I.InBox w := by
  have h : ∀ j, ∀ᵐ w ∂I.law, w j ∈ Set.Icc (I.lo j) (I.hi j) := by
    intro j
    have hm := measurePreserving_eval I.μ j
    have h1 : ∀ᵐ t ∂I.μ j, t ∈ Set.Icc (I.lo j) (I.hi j) := by
      rw [ae_iff]
      have := I.support j
      have e : {a : ℝ | ¬ a ∈ Set.Icc (I.lo j) (I.hi j)} = (Set.Icc (I.lo j) (I.hi j))ᶜ := rfl
      rw [e]; exact this
    exact hm.quasiMeasurePreserving.ae h1
  exact ae_all_iff.mpr h

lemma splice_box {I : Instance k} (i : Fin k) {v w : Fin k → ℝ} (hv : I.InBox v)
    (hw : I.InBox w) : I.InBox (splice i v w) := by
  intro j
  unfold splice
  split_ifs
  · exact hv j
  · exact hw j

lemma update_box {I : Instance k} {v : Fin k → ℝ} (hv : I.InBox v) (i : Fin k) {a : ℝ}
    (ha : a ∈ Set.Icc (I.lo i) (I.hi i)) : I.InBox (Function.update v i a) := by
  intro j
  by_cases h : j = i
  · subst h; simpa using ha
  · rw [Function.update_of_ne h]; exact hv j

lemma splice_splice_le {i j : Fin k} (h : i ≤ j) (v w w' : Fin k → ℝ) :
    splice j (splice i v w) w' = splice i v (splice j w w') := by
  funext l
  unfold splice
  by_cases h1 : l ≤ i
  · have : l ≤ j := le_trans h1 h
    simp [h1, this]
  · by_cases h2 : l ≤ j <;> simp [h1, h2]

lemma splice_splice_ge {i j : Fin k} (h : j ≤ i) (v w w' : Fin k → ℝ) :
    splice j (splice i v w) w' = splice j v w' := by
  funext l
  unfold splice
  by_cases h1 : l ≤ j
  · have : l ≤ i := le_trans h1 h
    simp [h1, this]
  · simp [h1]

lemma measurable_splice (i : Fin k) :
    Measurable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => splice i p.1 p.2) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  unfold splice
  by_cases h : j ≤ i
  · simp only [h, if_true]; exact (measurable_pi_apply j).comp measurable_fst
  · simp only [h, if_false]; exact (measurable_pi_apply j).comp measurable_snd

lemma splice_mp (I : Instance k) (i : Fin k) :
    MeasurePreserving (fun p : (Fin k → ℝ) × (Fin k → ℝ) => splice i p.1 p.2)
      (I.law.prod I.law) I.law := by
  refine ⟨measurable_splice i, ?_⟩
  unfold Instance.law
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  rw [Measure.map_apply (measurable_splice i) (MeasurableSet.univ_pi hs)]
  classical
  let s1 : ∀ j : Fin k, Set ℝ := fun j => if j ≤ i then s j else Set.univ
  let s2 : ∀ j : Fin k, Set ℝ := fun j => if j ≤ i then Set.univ else s j
  have hpre : (fun p : (Fin k → ℝ) × (Fin k → ℝ) => splice i p.1 p.2) ⁻¹' Set.univ.pi s
      = Set.univ.pi s1 ×ˢ Set.univ.pi s2 := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod, splice,
      s1, s2]
    constructor
    · intro h
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have := h j; split_ifs at this ⊢ with hj
        · exact this
        · trivial
      · have := h j; split_ifs at this ⊢ with hj
        · trivial
        · exact this
    · rintro ⟨h1, h2⟩ j
      have a := h1 j; have b := h2 j
      split_ifs at a b ⊢ with hj
      · exact a
      · exact b
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp only [s1, s2]
  split_ifs <;> simp

lemma integrable_splice_prod (I : Instance k) (i : Fin k) {G : (Fin k → ℝ) → ℝ}
    (hG : Integrable G I.law) :
    Integrable (fun p : (Fin k → ℝ) × (Fin k → ℝ) => G (splice i p.1 p.2)) (I.law.prod I.law) :=
  (splice_mp I i).integrable_comp_of_integrable hG

lemma integral_integral_splice (I : Instance k) (i : Fin k) {G : (Fin k → ℝ) → ℝ}
    (hG : Integrable G I.law) :
    ∫ v, (∫ w, G (splice i v w) ∂I.law) ∂I.law = ∫ v, G v ∂I.law := by
  rw [← integral_prod (fun p : (Fin k → ℝ) × (Fin k → ℝ) => G (splice i p.1 p.2))
    (integrable_splice_prod I i hG)]
  rw [← integral_map (splice_mp I i).measurable.aemeasurable
    (by rw [(splice_mp I i).map_eq]; exact hG.aestronglyMeasurable), (splice_mp I i).map_eq]

lemma integrable_integral_splice (I : Instance k) (i : Fin k) {G : (Fin k → ℝ) → ℝ}
    (hG : Integrable G I.law) :
    Integrable (fun v => ∫ w, G (splice i v w) ∂I.law) I.law :=
  (integrable_splice_prod I i hG).integral_prod_left

/-- the conditional expectation of a function of the future, given a fixed history, is integrable
in a later history -/
lemma integrable_cond_splice (I : Instance k) (i j : Fin k) (v : Fin k → ℝ)
    {G : (Fin k → ℝ) → ℝ} (hG : Integrable (fun u => G (splice i v u)) I.law) :
    Integrable (fun w => ∫ w', G (splice j (splice i v w) w') ∂I.law) I.law := by
  by_cases h : i ≤ j
  · simp_rw [splice_splice_le h]
    exact integrable_integral_splice I j hG
  · simp_rw [splice_splice_ge (le_of_lt (not_le.mp h))]
    exact integrable_const _

lemma measurable_cond (I : Instance k) (i : Fin k) {G : (Fin k → ℝ) → ℝ}
    (hG : Measurable G) : Measurable (fun v => ∫ w, G (splice i v w) ∂I.law) := by
  have : StronglyMeasurable (Function.uncurry fun v w => G (splice i v w)) :=
    (hG.comp (measurable_splice i)).stronglyMeasurable
  exact (this.integral_prod_right (ν := I.law)).measurable

lemma integrable_of_box_bound (I : Instance k) {f : (Fin k → ℝ) → ℝ} (hf : Measurable f)
    (C : ℝ) (hC : ∀ v, I.InBox v → |f v| ≤ C) : Integrable f I.law := by
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_box I] with v hv
  simpa [Real.norm_eq_abs] using hC v hv

lemma abs_mul_x_le (I : Instance k) {x : ℝ} {j : Fin k} {t : ℝ}
    (ht : t ∈ Set.Icc (I.lo j) (I.hi j)) (hx : x ∈ Set.Icc (0 : ℝ) 1) : |t * x| ≤ I.hi j := by
  have h0 : 0 ≤ t := le_trans (I.lo_nonneg j) ht.1
  rw [abs_of_nonneg (mul_nonneg h0 hx.1)]
  nlinarith [ht.2, hx.2, hx.1]

end SeqMechExPost.Optimal.SMAux


open MeasureTheory

namespace SeqMechExPost.Optimal.SMAux

open SeqMechExPost.Optimal

variable {k : ℕ}

/-- stage utility of an original mechanism -/
def su (M : SeqMech k) (j : Fin k) (v : Fin k → ℝ) : ℝ := v j * M.x j v - M.p j v

/-- the sum of stage utilities after day `i` -/
def F (M : SeqMech k) (i : Fin k) (u : Fin k → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => i < j), su M j u

lemma U_eq (I : Instance k) (M : SeqMech k) (i : Fin k) (v : Fin k → ℝ) :
    M.U I i v = ∫ w, F M i (splice i v w) ∂I.law := rfl

lemma adjust_pHat (I : Instance k) (M : SeqMech k) (i : Fin k) (v : Fin k → ℝ) :
    (adjust I M).pHat i v = M.p i v - M.U I i v := rfl

lemma unadjust_p (I : Instance k) (A : AdjMech k) (i : Fin k) (v : Fin k → ℝ) :
    (unadjust I A).p i v = A.pHat i v + A.nextU I i v := rfl

section adm

variable {I : Instance k} {M : SeqMech k} (hM : M.Admissible I)
include hM

lemma int_vx (j : Fin k) : Integrable (fun v => v j * M.x j v) I.law :=
  integrable_of_box_bound I ((measurable_pi_apply j).mul (hM.2.1 j).1) (I.hi j)
    (fun v hv => abs_mul_x_le I (hv j) (hM.2.2.1 j v hv))

lemma int_vx_splice (i j : Fin k) {v : Fin k → ℝ} (hv : I.InBox v) :
    Integrable (fun w => splice i v w j * M.x j (splice i v w)) I.law := by
  have hs : Measurable (fun w : Fin k → ℝ => splice i v w) :=
    (measurable_splice i).comp (measurable_const.prodMk measurable_id)
  exact integrable_of_box_bound I
    (((measurable_pi_apply j).comp hs).mul ((hM.2.1 j).1.comp hs)) (I.hi j)
    (fun w hw => abs_mul_x_le I (splice_box i hv hw j) (hM.2.2.1 j _ (splice_box i hv hw)))

lemma int_su (j : Fin k) : Integrable (su M j) I.law :=
  (int_vx hM j).sub (hM.2.2.2.1 j)

lemma int_su_splice (i j : Fin k) {v : Fin k → ℝ} (hv : I.InBox v) :
    Integrable (fun w => su M j (splice i v w)) I.law :=
  (int_vx_splice hM i j hv).sub (hM.2.2.2.2 i j v hv)

lemma meas_su (j : Fin k) : Measurable (su M j) :=
  ((measurable_pi_apply j).mul (hM.2.1 j).1).sub (hM.2.1 j).2

lemma int_F (i : Fin k) : Integrable (F M i) I.law := by
  unfold F
  exact integrable_finsetSum _ (fun j _ => int_su hM j)

lemma int_F_splice (i i' : Fin k) {v : Fin k → ℝ} (hv : I.InBox v) :
    Integrable (fun w => F M i (splice i' v w)) I.law := by
  unfold F
  exact integrable_finsetSum _ (fun j _ => int_su_splice hM i' j hv)

lemma meas_F (i : Fin k) : Measurable (F M i) := by
  unfold F
  exact Finset.measurable_sum _ (fun j _ => meas_su hM j)

lemma meas_U (i : Fin k) : Measurable (M.U I i) := by
  have : M.U I i = fun v => ∫ w, F M i (splice i v w) ∂I.law := rfl
  rw [this]; exact measurable_cond I i (meas_F hM i)

lemma int_U (i : Fin k) : Integrable (M.U I i) I.law := by
  have : M.U I i = fun v => ∫ w, F M i (splice i v w) ∂I.law := rfl
  rw [this]; exact integrable_integral_splice I i (int_F hM i)

lemma int_U_splice (i j : Fin k) {v : Fin k → ℝ} (hv : I.InBox v) :
    Integrable (fun w => M.U I j (splice i v w)) I.law := by
  simp_rw [U_eq]
  exact integrable_cond_splice I i j v (int_F_splice hM j i hv)

end adm

lemma U_dep (I : Instance k) (M : SeqMech k) (i : Fin k) (v v' : Fin k → ℝ)
    (h : ∀ j, j ≤ i → v j = v' j) : M.U I i v = M.U I i v' := by
  have : ∀ w, splice i v w = splice i v' w := by
    intro w; funext l; unfold splice; split_ifs with hl
    · exact h l hl
    · rfl
  simp_rw [U_eq, this]

lemma filter_succ (i : Fin k) (h : i.val + 1 < k) :
    Finset.univ.filter (fun l : Fin k => i < l)
      = insert (⟨i.val + 1, h⟩ : Fin k) (Finset.univ.filter (fun l : Fin k => (⟨i.val + 1, h⟩ : Fin k) < l)) := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.lt_def,
    Fin.ext_iff]
  omega

lemma U_last (I : Instance k) (M : SeqMech k) (i : Fin k) (h : ¬ i.val + 1 < k)
    (v : Fin k → ℝ) : M.U I i v = 0 := by
  rw [U_eq]
  have : ∀ u, F M i u = 0 := by
    intro u; unfold F
    apply Finset.sum_eq_zero
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def] at hl
    exact absurd l.isLt (by omega)
  simp [this]

lemma U_rec {I : Instance k} {M : SeqMech k} (hM : M.Admissible I) (i : Fin k)
    (h : i.val + 1 < k) {v : Fin k → ℝ} (hv : I.InBox v) :
    M.U I i v = ∫ w, (su M ⟨i.val + 1, h⟩ (splice i v w) + M.U I ⟨i.val + 1, h⟩ (splice i v w))
      ∂I.law := by
  set j : Fin k := ⟨i.val + 1, h⟩ with hj
  have hij : i ≤ j := by rw [Fin.le_def]; simp [hj]
  have hF : ∀ u, F M i u = su M j u + F M j u := by
    intro u; unfold F
    rw [filter_succ i h, Finset.sum_insert]
    simp
  have hUj : ∀ w, M.U I j (splice i v w) = ∫ w', F M j (splice i v (splice j w w')) ∂I.law := by
    intro w; rw [U_eq]; simp_rw [splice_splice_le hij]
  rw [integral_add (int_su_splice hM i j hv) (int_U_splice hM i j hv)]
  simp_rw [hUj]
  rw [integral_integral_splice I j (int_F_splice hM j i hv), ← integral_add
    (int_su_splice hM i j hv) (int_F_splice hM j i hv), U_eq]
  simp_rw [hF]

lemma nextU_adjust {I : Instance k} {M : SeqMech k} (hM : M.Admissible I) (i : Fin k)
    {v : Fin k → ℝ} (hv : I.InBox v) : (adjust I M).nextU I i v = M.U I i v := by
  unfold AdjMech.nextU
  split_ifs with h
  · rw [U_rec hM i h hv]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
    simp only [adjust_pHat, su]
    show _ * M.x _ _ - _ = _
    ring
  · exact (U_last I M i h v).symm

lemma adjust_admissible {I : Instance k} {M : SeqMech k} (hM : M.Admissible I) :
    (adjust I M).Admissible I := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i v w h
    refine ⟨(hM.1 i v w h).1, ?_⟩
    simp only [adjust_pHat]
    rw [(hM.1 i v w h).2, U_dep I M i v w h]
  · intro i
    exact ⟨(hM.2.1 i).1, (hM.2.1 i).2.sub (meas_U hM i)⟩
  · exact hM.2.2.1
  · intro i
    exact (hM.2.2.2.1 i).sub (int_U hM i)
  · intro i j v hv
    exact (hM.2.2.2.2 i j v hv).sub (int_U_splice hM i j hv)

/-- part (a) of Lemma 3 -/
lemma feasible_iff {I : Instance k} {M : SeqMech k} (hM : M.Admissible I) :
    M.Feasible I ↔ (adjust I M).AdjFeasible I := by
  constructor
  · rintro ⟨_, hPIC, hIR⟩
    refine ⟨adjust_admissible hM, ?_, ?_⟩
    · intro i v hv a ha
      have := hPIC i v hv a ha
      simp only [adjust_pHat]
      show v i * M.x i _ - _ ≤ v i * M.x i v - _
      linarith
    · intro i v hv
      rw [nextU_adjust hM i hv, adjust_pHat]
      have := hIR i v hv
      show _ ≤ v i * M.x i v - _
      linarith
  · rintro ⟨_, hIC, hUB⟩
    refine ⟨hM, ?_, ?_⟩
    · intro i v hv a ha
      have := hIC i v hv a ha
      simp only [adjust_pHat] at this
      change v i * M.x i _ - _ ≤ v i * M.x i v - _ at this
      linarith
    · intro i v hv
      have := hUB i v hv
      rw [nextU_adjust hM i hv, adjust_pHat] at this
      change _ ≤ v i * M.x i v - _ at this
      linarith

/-- part (b) of Lemma 3 -/
lemma revenue_eq {I : Instance k} {M : SeqMech k} (hM : M.Admissible I) :
    M.revenue I = (adjust I M).adjObj I := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp [SeqMech.revenue, AdjMech.adjObj]
  set i0 : Fin k := ⟨0, hk⟩ with hi0
  have hpt : ∀ v, (∑ i, (if i.val = 0 then (adjust I M).pHat i v else v i * (adjust I M).x i v))
      = (∑ i, M.p i v) - M.U I i0 v + F M i0 v := by
    intro v
    have e1 : ∀ i : Fin k, (if i.val = 0 then (adjust I M).pHat i v else v i * (adjust I M).x i v)
        = M.p i v + (if i.val = 0 then - M.U I i v else su M i v) := by
      intro i
      split_ifs
      · rw [adjust_pHat]; ring
      · simp only [su]; show v i * M.x i v = _; ring
    rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_add_distrib, Finset.sum_ite]
    have hf1 : Finset.univ.filter (fun i : Fin k => i.val = 0) = {i0} := by
      ext l; simp [hi0, Fin.ext_iff]
    have hf2 : Finset.univ.filter (fun i : Fin k => ¬ i.val = 0)
        = Finset.univ.filter (fun i : Fin k => i0 < i) := by
      ext l; simp [hi0, Fin.lt_def]
    rw [hf1, hf2, Finset.sum_singleton]
    unfold F
    ring
  unfold AdjMech.adjObj
  simp_rw [hpt]
  have hsum : Integrable (fun v => ∑ i, M.p i v) I.law :=
    integrable_finsetSum _ (fun i _ => hM.2.2.2.1 i)
  have h1 : Integrable (fun v => ∑ i, M.p i v - M.U I i0 v) I.law := hsum.sub (int_U hM i0)
  rw [integral_add h1 (int_F hM i0), integral_sub hsum (int_U hM i0)]
  have : ∫ v, M.U I i0 v ∂I.law = ∫ v, F M i0 v ∂I.law := by
    simp_rw [U_eq]; exact integral_integral_splice I i0 (int_F hM i0)
  rw [this]
  unfold SeqMech.revenue
  ring

section part2

variable {I : Instance k} {A : AdjMech k} (hA : A.AdjFeasible I)
include hA

/-- adjusted stage utility -/
def tu (A : AdjMech k) (j : Fin k) (u : Fin k → ℝ) : ℝ := u j * A.x j u - A.pHat j u

lemma int_tu (j : Fin k) : Integrable (tu A j) I.law := by
  have h1 : Integrable (fun v => v j * A.x j v) I.law :=
    integrable_of_box_bound I ((measurable_pi_apply j).mul (hA.1.2.1 j).1) (I.hi j)
      (fun v hv => abs_mul_x_le I (hv j) (hA.1.2.2.1 j v hv))
  exact h1.sub (hA.1.2.2.2.1 j)

lemma int_tu_splice (i j : Fin k) {v : Fin k → ℝ} (hv : I.InBox v) :
    Integrable (fun w => tu A j (splice i v w)) I.law := by
  have hs : Measurable (fun w : Fin k → ℝ => splice i v w) :=
    (measurable_splice i).comp (measurable_const.prodMk measurable_id)
  have h1 : Integrable (fun w => splice i v w j * A.x j (splice i v w)) I.law :=
    integrable_of_box_bound I
      (((measurable_pi_apply j).comp hs).mul ((hA.1.2.1 j).1.comp hs)) (I.hi j)
      (fun w hw => abs_mul_x_le I (splice_box i hv hw j) (hA.1.2.2.1 j _ (splice_box i hv hw)))
  exact h1.sub (hA.1.2.2.2.2 i j v hv)

lemma nextU_eq (i : Fin k) (h : i.val + 1 < k) (v : Fin k → ℝ) :
    A.nextU I i v = ∫ w, tu A ⟨i.val + 1, h⟩ (splice i v w) ∂I.law := by
  unfold AdjMech.nextU; rw [dif_pos h]; rfl

lemma nextU_last (i : Fin k) (h : ¬ i.val + 1 < k) (v : Fin k → ℝ) : A.nextU I i v = 0 := by
  unfold AdjMech.nextU; rw [dif_neg h]

lemma meas_nextU (i : Fin k) : Measurable (A.nextU I i) := by
  by_cases h : i.val + 1 < k
  · have : A.nextU I i = fun v => ∫ w, tu A ⟨i.val + 1, h⟩ (splice i v w) ∂I.law :=
      funext (nextU_eq hA i h)
    rw [this]
    exact measurable_cond I i (((measurable_pi_apply _).mul (hA.1.2.1 _).1).sub (hA.1.2.1 _).2)
  · have : A.nextU I i = fun _ => 0 := funext (nextU_last hA i h)
    rw [this]; exact measurable_const

lemma int_nextU (i : Fin k) : Integrable (A.nextU I i) I.law := by
  by_cases h : i.val + 1 < k
  · have : A.nextU I i = fun v => ∫ w, tu A ⟨i.val + 1, h⟩ (splice i v w) ∂I.law :=
      funext (nextU_eq hA i h)
    rw [this]
    exact integrable_integral_splice I i (int_tu hA _)
  · have : A.nextU I i = fun _ => 0 := funext (nextU_last hA i h)
    rw [this]; exact integrable_const _

lemma int_nextU_splice (i j : Fin k) {v : Fin k → ℝ} (hv : I.InBox v) :
    Integrable (fun w => A.nextU I j (splice i v w)) I.law := by
  by_cases h : j.val + 1 < k
  · simp_rw [nextU_eq hA j h]
    exact integrable_cond_splice I i j v (int_tu_splice hA i _ hv)
  · simp_rw [nextU_last hA j h]; exact integrable_const _

lemma nextU_dep (i : Fin k) (v v' : Fin k → ℝ) (hvv : ∀ j, j ≤ i → v j = v' j) :
    A.nextU I i v = A.nextU I i v' := by
  have : ∀ w, splice i v w = splice i v' w := by
    intro w; funext l; unfold splice; split_ifs with hl
    · exact hvv l hl
    · rfl
  unfold AdjMech.nextU
  simp_rw [this]

lemma unadjust_admissible : (unadjust I A).Admissible I := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i v w h
    refine ⟨(hA.1.1 i v w h).1, ?_⟩
    simp only [unadjust_p]
    rw [(hA.1.1 i v w h).2, nextU_dep hA i v w h]
  · intro i
    exact ⟨(hA.1.2.1 i).1, (hA.1.2.1 i).2.add (meas_nextU hA i)⟩
  · exact hA.1.2.2.1
  · intro i
    exact (hA.1.2.2.2.1 i).add (int_nextU hA i)
  · intro i j v hv
    exact (hA.1.2.2.2.2 i j v hv).add (int_nextU_splice hA i j hv)

lemma U_unadjust : ∀ n : ℕ, ∀ i : Fin k, i.val + n + 1 = k → ∀ v, I.InBox v →
    (unadjust I A).U I i v = A.nextU I i v := by
  intro n
  induction n with
  | zero =>
    intro i hi v _
    have h : ¬ i.val + 1 < k := by omega
    rw [U_last I _ i h, nextU_last hA i h]
  | succ n ih =>
    intro i hi v hv
    have h : i.val + 1 < k := by omega
    rw [U_rec (unadjust_admissible hA) i h hv, nextU_eq hA i h]
    refine integral_congr_ae ?_
    filter_upwards [ae_box I] with w hw
    have hb := splice_box i hv hw
    rw [ih ⟨i.val + 1, h⟩ (by simp; omega) _ hb]
    simp only [su, tu, unadjust_p]
    show _ * A.x _ _ - _ + _ = _
    ring

lemma U_unadjust' (i : Fin k) {v : Fin k → ℝ} (hv : I.InBox v) :
    (unadjust I A).U I i v = A.nextU I i v :=
  U_unadjust hA (k - 1 - i.val) i (by have := i.isLt; omega) v hv

lemma unadjust_feasible : (unadjust I A).Feasible I := by
  refine ⟨unadjust_admissible hA, ?_, ?_⟩
  · intro i v hv a ha
    have hb := update_box hv i ha
    rw [U_unadjust' hA i hb, U_unadjust' hA i hv, unadjust_p, unadjust_p]
    have := hA.2.1 i v hv a ha
    show v i * A.x i _ - _ + _ ≤ v i * A.x i v - _ + _
    linarith
  · intro i v hv
    rw [unadjust_p]
    have := hA.2.2 i v hv
    show 0 ≤ v i * A.x i v - _
    linarith

lemma adjust_unadjust (i : Fin k) {v : Fin k → ℝ} (hv : I.InBox v) :
    (adjust I (unadjust I A)).pHat i v = A.pHat i v := by
  rw [adjust_pHat, U_unadjust' hA i hv, unadjust_p]; ring

lemma adjObj_adjust_unadjust : (adjust I (unadjust I A)).adjObj I = A.adjObj I := by
  unfold AdjMech.adjObj
  refine integral_congr_ae ?_
  filter_upwards [ae_box I] with v hv
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs
  · exact adjust_unadjust hA i hv
  · rfl

end part2

theorem lemma3_main (I : Instance k) :
    (∀ M : SeqMech k, M.Admissible I →
      (M.Feasible I ↔ (adjust I M).AdjFeasible I) ∧
      M.revenue I = (adjust I M).adjObj I ∧
      (∀ i v, I.InBox v → (unadjust I (adjust I M)).p i v = M.p i v) ∧
      (M.IsOptimal I ↔ (adjust I M).AdjOptimal I)) ∧
    (∀ A : AdjMech k, A.AdjFeasible I →
      (unadjust I A).Feasible I ∧
      ∀ i v, I.InBox v → (adjust I (unadjust I A)).pHat i v = A.pHat i v) := by
  refine ⟨fun M hM => ⟨feasible_iff hM, revenue_eq hM, ?_, ?_⟩,
    fun A hA => ⟨unadjust_feasible hA, fun i v hv => adjust_unadjust hA i hv⟩⟩
  · intro i v hv
    rw [unadjust_p, nextU_adjust hM i hv, adjust_pHat]; ring
  · constructor
    · rintro ⟨hF, hopt⟩
      refine ⟨(feasible_iff hM).mp hF, fun A' hA' => ?_⟩
      have h1 := hopt _ (unadjust_feasible hA')
      rw [revenue_eq (unadjust_admissible hA'), adjObj_adjust_unadjust hA',
        revenue_eq hM] at h1
      exact h1
    · rintro ⟨hF, hopt⟩
      refine ⟨(feasible_iff hM).mpr hF, fun M' hM' => ?_⟩
      rw [revenue_eq hM'.1, revenue_eq hM]
      exact hopt _ ((feasible_iff hM'.1).mp hM')

end SeqMechExPost.Optimal.SMAux


open SeqMechExPost.Optimal

theorem solution {k : ℕ} (I : Instance k) :
    (∀ M : SeqMech k, M.Admissible I →
      (M.Feasible I ↔ (adjust I M).AdjFeasible I) ∧
      M.revenue I = (adjust I M).adjObj I ∧
      (∀ i v, I.InBox v → (unadjust I (adjust I M)).p i v = M.p i v) ∧
      (M.IsOptimal I ↔ (adjust I M).AdjOptimal I)) ∧
    (∀ A : AdjMech k, A.AdjFeasible I →
      (unadjust I A).Feasible I ∧
      ∀ i v, I.InBox v → (adjust I (unadjust I A)).pHat i v = A.pHat i v) :=
  SeqMechExPost.Optimal.SMAux.lemma3_main I
