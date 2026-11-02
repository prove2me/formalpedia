-- Prove2me | solution 1 for SeqMechExPost.Optimal.lemma_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T12:08:04.390451+00:00
-- url     : https://prove2.me/submissions/a3ac062f-91eb-4ceb-8733-15b4c1ab7ba6

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


open MeasureTheory

namespace SeqMechExPost.Optimal.SMAux

open SeqMechExPost.Optimal

variable {k : ℕ}

/-! ### the update map preserves the law -/

lemma update_mp (I : Instance k) (j : Fin k) :
    MeasurePreserving (fun p : (Fin k → ℝ) × ℝ => Function.update p.1 j p.2)
      (I.law.prod (I.μ j)) I.law := by
  refine ⟨measurable_update', ?_⟩
  unfold Instance.law
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  classical
  let s' : ∀ l : Fin k, Set ℝ := Function.update s j Set.univ
  have hpre : (fun p : (Fin k → ℝ) × ℝ => Function.update p.1 j p.2) ⁻¹' Set.univ.pi s
      = Set.univ.pi s' ×ˢ s j := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod, s']
    constructor
    · intro h
      refine ⟨fun l => ?_, ?_⟩
      · by_cases hl : l = j
        · subst hl; simp
        · have := h l; rw [Function.update_of_ne hl] at this ⊢; exact this
      · have := h j; simpa using this
    · rintro ⟨h1, h2⟩ l
      by_cases hl : l = j
      · subst hl; simpa using h2
      · have := h1 l; rw [Function.update_of_ne hl] at this ⊢; exact this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ (fun l => I.μ l (s' l)) (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun l => I.μ l (s l)) (Finset.mem_univ j)]
  have e : ∏ l ∈ Finset.univ.erase j, I.μ l (s' l) = ∏ l ∈ Finset.univ.erase j, I.μ l (s l) := by
    refine Finset.prod_congr rfl (fun l hl => ?_)
    simp only [s', Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [e]
  simp [s']
  ring

lemma integrable_update_prod (I : Instance k) (j : Fin k) {G : (Fin k → ℝ) → ℝ}
    (hG : Integrable G I.law) :
    Integrable (fun p : (Fin k → ℝ) × ℝ => G (Function.update p.1 j p.2)) (I.law.prod (I.μ j)) :=
  (update_mp I j).integrable_comp_of_integrable hG

lemma integral_integral_update (I : Instance k) (j : Fin k) {G : (Fin k → ℝ) → ℝ}
    (hG : Integrable G I.law) :
    ∫ v, (∫ t, G (Function.update v j t) ∂I.μ j) ∂I.law = ∫ v, G v ∂I.law := by
  rw [← integral_prod (fun p : (Fin k → ℝ) × ℝ => G (Function.update p.1 j p.2))
    (integrable_update_prod I j hG)]
  rw [← integral_map (update_mp I j).measurable.aemeasurable
    (by rw [(update_mp I j).map_eq]; exact hG.aestronglyMeasurable), (update_mp I j).map_eq]

lemma integrable_integral_update (I : Instance k) (j : Fin k) {G : (Fin k → ℝ) → ℝ}
    (hG : Integrable G I.law) :
    Integrable (fun v => ∫ t, G (Function.update v j t) ∂I.μ j) I.law :=
  (integrable_update_prod I j hG).integral_prod_left

/-! ### evaluation at one coordinate -/

lemma integral_eval (I : Instance k) (j : Fin k) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ w, f (w j) ∂I.law = ∫ t, f t ∂I.μ j := by
  have hmp := measurePreserving_eval I.μ j
  unfold Instance.law
  rw [← integral_map hmp.measurable.aemeasurable (by rw [hmp.map_eq]; exact hf.aestronglyMeasurable),
    hmp.map_eq]

lemma integrable_of_eval (I : Instance k) (j : Fin k) {f : ℝ → ℝ} (hf : Measurable f)
    (h : Integrable (fun w => f (w j)) I.law) : Integrable f (I.μ j) := by
  have hmp := measurePreserving_eval I.μ j
  unfold Instance.law at h
  exact (hmp.integrable_comp hf.aestronglyMeasurable).mp h

lemma ae_Icc (I : Instance k) (j : Fin k) : ∀ᵐ t ∂I.μ j, t ∈ Set.Icc (I.lo j) (I.hi j) := by
  rw [ae_iff]
  have := I.support j
  have e : {a : ℝ | ¬ a ∈ Set.Icc (I.lo j) (I.hi j)} = (Set.Icc (I.lo j) (I.hi j))ᶜ := rfl
  rw [e]; exact this

lemma integrable_of_Icc_bound (I : Instance k) (j : Fin k) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (I.μ j))
    (C : ℝ) (hC : ∀ t ∈ Set.Icc (I.lo j) (I.hi j), |f t| ≤ C) : Integrable f (I.μ j) := by
  refine Integrable.of_bound hf C ?_
  filter_upwards [ae_Icc I j] with t ht
  simpa [Real.norm_eq_abs] using hC t ht

/-! ### static mechanisms -/

/-- utility bounds for a feasible static mechanism of the tight problem -/
lemma static_bounds {ν : Measure ℝ} [IsProbabilityMeasure ν] {lo hi : ℝ} (hlh : lo ≤ hi)
    (hlo : 0 ≤ lo) (hsupp : ν (Set.Icc lo hi)ᶜ = 0)
    {g : ℝ → ℝ} {c : ℝ} {m : StaticMech} (hm : TradeoffFeasible ν lo hi g c m) :
    ∀ t ∈ Set.Icc lo hi, 0 ≤ t * m.x t - m.p t ∧ t * m.x t - m.p t ≤ c + (hi - lo) := by
  obtain ⟨hmx, hmp, hx01, hIC, hIR, hpint, _, hint⟩ := hm
  have hlo' : lo ∈ Set.Icc lo hi := ⟨le_rfl, hlh⟩
  have hmono : ∀ t ∈ Set.Icc lo hi, lo * m.x lo - m.p lo ≤ t * m.x t - m.p t := by
    intro t ht
    have := hIC t ht lo hlo'
    have hx := hx01 lo hlo'
    nlinarith [ht.1, hx.1]
  have hae : ∀ᵐ t ∂ν, t ∈ Set.Icc lo hi := by
    rw [ae_iff]
    have e : {a : ℝ | ¬ a ∈ Set.Icc lo hi} = (Set.Icc lo hi)ᶜ := rfl
    rw [e]; exact hsupp
  have hu_int : Integrable (fun t => t * m.x t - m.p t) ν := by
    refine Integrable.sub ?_ hpint
    refine Integrable.of_bound (measurable_id.mul hmx).aestronglyMeasurable hi ?_
    filter_upwards [hae] with t ht
    have hx := hx01 t ht
    have h0 : 0 ≤ t := le_trans hlo ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 hx.1)]
    nlinarith [ht.2, hx.2, hx.1]
  have hlo_le : lo * m.x lo - m.p lo ≤ c := by
    rw [← hint]
    have : ∫ _t, (lo * m.x lo - m.p lo) ∂ν = lo * m.x lo - m.p lo := by simp
    rw [← this]
    refine integral_mono_ae (integrable_const _) hu_int ?_
    filter_upwards [hae] with t ht
    exact hmono t ht
  intro t ht
  refine ⟨hIR t ht, ?_⟩
  have := hIC lo hlo' t ht
  have hx := hx01 t ht
  have h2 : (t - lo) * m.x t ≤ (hi - lo) * 1 :=
    mul_le_mul (by linarith [ht.2]) hx.2 hx.1 (by linarith [hlh])
  nlinarith [ht.1, hx.2, hx.1]

/-! ### the state of Theorem 7 -/

lemma cState_succ (X P : Fin k → ℝ → ℝ → ℝ) (c0 : ℝ) (i : Fin k) (v : Fin k → ℝ) :
    cState X P c0 (i.val + 1) v
      = v i * X i (cState X P c0 i.val v) (v i) - P i (cState X P c0 i.val v) (v i) := by
  have hi : 0 + i.val < k := by simp
  have e : (⟨0 + i.val, hi⟩ : Fin k) = i := Fin.ext (by simp)
  show runState X P 0 (fun _ => c0) (i.val + 1) v = _
  rw [runState, dif_pos hi, e]
  rfl

lemma cState_succ_ge (X P : Fin k → ℝ → ℝ → ℝ) (c0 : ℝ) (n : ℕ) (hn : ¬ n < k)
    (v : Fin k → ℝ) : cState X P c0 (n + 1) v = 0 := by
  show runState X P 0 (fun _ => c0) (n + 1) v = _
  rw [runState, dif_neg (by omega)]

lemma cState_dep (X P : Fin k → ℝ → ℝ → ℝ) (c0 : ℝ) :
    ∀ n (v w : Fin k → ℝ), (∀ j : Fin k, j.val < n → v j = w j) →
      cState X P c0 n v = cState X P c0 n w := by
  intro n
  induction n with
  | zero => intro v w _; rfl
  | succ n ih =>
    intro v w h
    by_cases hn : n < k
    · have h' := ih v w (fun j hj => h j (by omega))
      rw [cState_succ X P c0 ⟨n, hn⟩ v, cState_succ X P c0 ⟨n, hn⟩ w]
      simp only at h' ⊢
      rw [h', h ⟨n, hn⟩ (by simp)]
    · rw [cState_succ_ge X P c0 n hn, cState_succ_ge X P c0 n hn]

lemma meas_comp (F : ℝ → ℝ → ℝ) (hF : Measurable (Function.uncurry F))
    {f g : (Fin k → ℝ) → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun v => F (f v) (g v)) :=
  hF.comp (hf.prodMk hg)

lemma cState_meas (X P : Fin k → ℝ → ℝ → ℝ)
    (hmeas : ∀ i, Measurable (Function.uncurry (X i)) ∧ Measurable (Function.uncurry (P i)))
    (c0 : ℝ) : ∀ n, Measurable (cState X P c0 n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    by_cases hn : n < k
    · have e : cState X P c0 (n + 1) = fun v =>
          v ⟨n, hn⟩ * X ⟨n, hn⟩ (cState X P c0 n v) (v ⟨n, hn⟩)
            - P ⟨n, hn⟩ (cState X P c0 n v) (v ⟨n, hn⟩) := by
        funext v; exact cState_succ X P c0 ⟨n, hn⟩ v
      rw [e]
      exact ((measurable_pi_apply _).mul
        (meas_comp _ (hmeas _).1 ih (measurable_pi_apply _))).sub
        (meas_comp _ (hmeas _).2 ih (measurable_pi_apply _))
    · have e : cState X P c0 (n + 1) = fun _ => 0 := by
        funext v; exact cState_succ_ge X P c0 n hn v
      rw [e]; exact measurable_const

lemma cState_nonneg {I : Instance k} (X P : Fin k → ℝ → ℝ → ℝ)
    (hopt : ∀ i c, 0 ≤ c → IsOptimizer I i c ⟨X i c, P i c⟩) (c0 : ℝ) (hc0 : 0 ≤ c0)
    (v : Fin k → ℝ) (hv : I.InBox v) : ∀ n, 0 ≤ cState X P c0 n v := by
  intro n
  induction n with
  | zero => exact hc0
  | succ n ih =>
    by_cases hn : n < k
    · rw [cState_succ X P c0 ⟨n, hn⟩ v]
      exact (hopt ⟨n, hn⟩ _ ih).1.2.2.2.2.1 _ (hv _)
    · rw [cState_succ_ge X P c0 n hn]

/-- total width of the type intervals -/
noncomputable def Dw (I : Instance k) : ℝ := ∑ j, (I.hi j - I.lo j)

lemma Dw_nonneg (I : Instance k) : 0 ≤ Dw I :=
  Finset.sum_nonneg (fun j _ => sub_nonneg.mpr (I.lo_le_hi j))

lemma gap_le_Dw (I : Instance k) (j : Fin k) : I.hi j - I.lo j ≤ Dw I :=
  Finset.single_le_sum (f := fun j => I.hi j - I.lo j)
    (fun j _ => sub_nonneg.mpr (I.lo_le_hi j)) (Finset.mem_univ j)

lemma cState_le {I : Instance k} (X P : Fin k → ℝ → ℝ → ℝ)
    (hopt : ∀ i c, 0 ≤ c → IsOptimizer I i c ⟨X i c, P i c⟩) (c0 : ℝ) (hc0 : 0 ≤ c0)
    (v : Fin k → ℝ) (hv : I.InBox v) : ∀ n, cState X P c0 n v ≤ c0 + n * Dw I := by
  intro n
  induction n with
  | zero => simp [cState, runState]
  | succ n ih =>
    by_cases hn : n < k
    · rw [cState_succ X P c0 ⟨n, hn⟩ v]
      have hc := cState_nonneg X P hopt c0 hc0 v hv n
      have hb := (static_bounds (I.lo_le_hi _) (I.lo_nonneg _) (I.support _)
        (hopt ⟨n, hn⟩ _ hc).1 (v ⟨n, hn⟩) (hv _)).2
      have := gap_le_Dw I ⟨n, hn⟩
      push_cast
      simp only at hb ih
      linarith
    · rw [cState_succ_ge X P c0 n hn]
      have := Dw_nonneg I
      positivity

end SeqMechExPost.Optimal.SMAux


open MeasureTheory

namespace SeqMechExPost.Optimal.SMAux

open SeqMechExPost.Optimal

variable {k : ℕ}

section static

variable {ν : Measure ℝ} [IsProbabilityMeasure ν] {lo hi : ℝ}

lemma ae_Icc' (hsupp : ν (Set.Icc lo hi)ᶜ = 0) : ∀ᵐ t ∂ν, t ∈ Set.Icc lo hi := by
  rw [ae_iff]
  have e : {a : ℝ | ¬ a ∈ Set.Icc lo hi} = (Set.Icc lo hi)ᶜ := rfl
  rw [e]; exact hsupp

lemma int_tx (hlo : 0 ≤ lo) (hsupp : ν (Set.Icc lo hi)ᶜ = 0) {x : ℝ → ℝ} (hx : Measurable x)
    (hx01 : ∀ v ∈ Set.Icc lo hi, x v ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun t => t * x t) ν := by
  refine Integrable.of_bound (measurable_id.mul hx).aestronglyMeasurable hi ?_
  filter_upwards [ae_Icc' hsupp] with t ht
  have h := hx01 t ht
  have h0 : 0 ≤ t := le_trans hlo ht.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 h.1)]
  nlinarith [ht.2, h.2, h.1]

lemma monotone_clip {g : ℝ → ℝ} (hg : MonotoneOn g (Set.Ici 0)) :
    Monotone (fun c => g (max c 0)) := by
  intro a b hab
  exact hg (by simp) (by simp) (max_le_max hab le_rfl)

lemma int_shift (hlo : 0 ≤ lo) (hsupp : ν (Set.Icc lo hi)ᶜ = 0) {g : ℝ → ℝ} {B : ℝ}
    (hg0 : ∀ u, 0 ≤ u → 0 ≤ g u) (hgB : ∀ u, g u ≤ B) (hgm : MonotoneOn g (Set.Ici 0))
    {m : StaticMech} (hmx : Measurable m.x) (hmp : Measurable m.p)
    (hx01 : ∀ v ∈ Set.Icc lo hi, m.x v ∈ Set.Icc (0 : ℝ) 1)
    (hIR : ∀ v ∈ Set.Icc lo hi, 0 ≤ v * m.x v - m.p v) {δ : ℝ} (hδ : 0 ≤ δ) :
    Integrable (fun t => t * m.x t + g (t * m.x t - m.p t + δ)) ν := by
  refine (int_tx hlo hsupp hmx hx01).add ?_
  have hmeas : Measurable (fun t => (fun c => g (max c 0)) (t * m.x t - m.p t + δ)) :=
    (monotone_clip hgm).measurable.comp (((measurable_id.mul hmx).sub hmp).add measurable_const)
  refine Integrable.of_bound (hmeas.aestronglyMeasurable.congr ?_) (max B 0) ?_
  · filter_upwards [ae_Icc' hsupp] with t ht
    have := hIR t ht
    show g (max _ 0) = _
    rw [max_eq_left (by linarith)]
  · filter_upwards [ae_Icc' hsupp] with t ht
    have := hIR t ht
    have h1 := hg0 _ (by linarith : 0 ≤ t * m.x t - m.p t + δ)
    rw [Real.norm_eq_abs, abs_of_nonneg h1]
    exact le_trans (hgB _) (le_max_left _ _)

lemma obj_le (hsupp : ν (Set.Icc lo hi)ᶜ = 0) {g : ℝ → ℝ} {c K : ℝ} {m : StaticMech}
    (hm : TradeoffFeasible ν lo hi g c m)
    (hK : ∀ t ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ u, 0 ≤ u → t * x + g u ≤ K) :
    tradeoffObj ν g m ≤ K := by
  obtain ⟨_, _, hx01, _, hIR, _, hobj, _⟩ := hm
  unfold tradeoffObj
  have : ∫ _t, K ∂ν = K := by simp
  rw [← this]
  refine integral_mono_ae hobj (integrable_const _) ?_
  filter_upwards [ae_Icc' hsupp] with t ht
  exact hK t ht _ (hx01 t ht) _ (hIR t ht)

lemma bdd_obj (hsupp : ν (Set.Icc lo hi)ᶜ = 0) {g : ℝ → ℝ} {c K : ℝ}
    (hK : ∀ t ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ u, 0 ≤ u → t * x + g u ≤ K) :
    BddAbove (tradeoffObj ν g '' {m | TradeoffFeasible ν lo hi g c m}) := by
  refine ⟨K, ?_⟩
  rintro _ ⟨m, hm, rfl⟩
  exact obj_le hsupp hm hK

lemma le_value (hsupp : ν (Set.Icc lo hi)ᶜ = 0) {g : ℝ → ℝ} {c K : ℝ}
    (hK : ∀ t ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ u, 0 ≤ u → t * x + g u ≤ K)
    {m : StaticMech} (hm : TradeoffFeasible ν lo hi g c m) :
    tradeoffObj ν g m ≤ tradeoffValue ν lo hi g c :=
  le_csSup (bdd_obj hsupp hK) ⟨m, hm, rfl⟩

lemma value_props (hlh : lo ≤ hi) (hlo : 0 ≤ lo) (hsupp : ν (Set.Icc lo hi)ᶜ = 0)
    {g : ℝ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hg0 : ∀ u, 0 ≤ u → 0 ≤ g u) (hgB : ∀ u, g u ≤ B) (hgm : MonotoneOn g (Set.Ici 0)) :
    (∀ c, 0 ≤ c → 0 ≤ tradeoffValue ν lo hi g c) ∧
    (∀ c, tradeoffValue ν lo hi g c ≤ hi + B) ∧
    MonotoneOn (tradeoffValue ν lo hi g) (Set.Ici 0) := by
  have hhi : 0 ≤ hi := le_trans hlo hlh
  have hK : ∀ t ∈ Set.Icc lo hi, ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ u, 0 ≤ u → t * x + g u ≤ hi + B := by
    intro t ht x hx u _
    have h0 : 0 ≤ t := le_trans hlo ht.1
    have : t * x ≤ hi := by nlinarith [ht.2, hx.1, hx.2]
    linarith [hgB u]
  have hnonneg : ∀ c, 0 ≤ c → 0 ≤ tradeoffValue ν lo hi g c := by
    intro c hc
    let m0 : StaticMech := ⟨fun _ => 0, fun _ => -c⟩
    have hm0 : TradeoffFeasible ν lo hi g c m0 := by
      refine ⟨measurable_const, measurable_const, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro v _; simp [m0]
      · intro v _ v' _; simp [m0]
      · intro v _; simp [m0, hc]
      · simp only [m0]; exact integrable_const _
      · simp only [m0, mul_zero, zero_sub, neg_neg, zero_add]; exact integrable_const _
      · simp [m0]
    have := le_value hsupp hK hm0
    have e : tradeoffObj ν g m0 = g c := by simp [tradeoffObj, m0]
    rw [e] at this
    linarith [hg0 c hc]
  refine ⟨hnonneg, ?_, ?_⟩
  · intro c
    by_cases hne : {m | TradeoffFeasible ν lo hi g c m}.Nonempty
    · refine csSup_le (hne.image _) ?_
      rintro _ ⟨m, hm, rfl⟩
      exact obj_le hsupp hm hK
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      unfold tradeoffValue
      rw [hne, Set.image_empty, Real.sSup_empty]
      linarith
  · intro c hc c' hc' hcc'
    simp only [Set.mem_Ici] at hc hc'
    by_cases hne : {m | TradeoffFeasible ν lo hi g c m}.Nonempty
    · refine csSup_le (hne.image _) ?_
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨hmx, hmp, hx01, hIC, hIR, hpint, hobj, hint⟩ := hm
      set δ := c' - c with hδ
      have hδ0 : 0 ≤ δ := by linarith
      let m' : StaticMech := ⟨m.x, fun t => m.p t - δ⟩
      have hu_int : Integrable (fun t => t * m.x t - m.p t) ν :=
        (int_tx hlo hsupp hmx hx01).sub hpint
      have hm' : TradeoffFeasible ν lo hi g c' m' := by
        refine ⟨hmx, hmp.sub measurable_const, hx01, ?_, ?_, hpint.sub (integrable_const _), ?_, ?_⟩
        · intro v hv v' hv'
          have := hIC v hv v' hv'
          simp only [m']; linarith
        · intro v hv
          have := hIR v hv
          simp only [m']; linarith
        · have := int_shift hlo hsupp hg0 hgB hgm hmx hmp hx01 hIR hδ0
          simp only [m']
          refine this.congr (Filter.Eventually.of_forall (fun t => ?_))
          simp only; ring_nf
        · simp only [m']
          have e : ∀ t, t * m.x t - (m.p t - δ) = (t * m.x t - m.p t) + δ := fun t => by ring
          simp_rw [e]
          rw [integral_add hu_int (integrable_const _), hint]
          simp [hδ]
      refine le_trans ?_ (le_value hsupp hK hm')
      unfold tradeoffObj
      refine integral_mono_ae hobj hm'.2.2.2.2.2.2.1 ?_
      filter_upwards [ae_Icc' hsupp] with t ht
      have := hIR t ht
      simp only [m']
      have h2 : g (t * m.x t - m.p t) ≤ g (t * m.x t - (m.p t - δ)) :=
        hgm (Set.mem_Ici.mpr this) (Set.mem_Ici.mpr (by linarith)) (by linarith)
      linarith
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      have : tradeoffValue ν lo hi g c = 0 := by
        unfold tradeoffValue
        rw [hne, Set.image_empty, Real.sSup_empty]
      rw [this]
      exact hnonneg c' hc'

end static

/-- sum of the upper ends of the type intervals -/
noncomputable def Hs (I : Instance k) : ℝ := ∑ j, I.hi j

lemma hi_nonneg (I : Instance k) (j : Fin k) : 0 ≤ I.hi j := le_trans (I.lo_nonneg j) (I.lo_le_hi j)

lemma Hs_nonneg (I : Instance k) : 0 ≤ Hs I := Finset.sum_nonneg (fun j _ => hi_nonneg I j)

lemma hi_le_Hs (I : Instance k) (j : Fin k) : I.hi j ≤ Hs I :=
  Finset.single_le_sum (f := fun j => I.hi j) (fun j _ => hi_nonneg I j) (Finset.mem_univ j)

lemma gTail_succ (I : Instance k) (j : Fin k) :
    gTail I (k - 1 - j.val + 1) = tradeoffValue (I.μ j) (I.lo j) (I.hi j) (gTail I (k - 1 - j.val)) := by
  have hm : k - 1 - j.val < k := by omega
  rw [gTail, dif_pos hm]
  have e : (⟨k - 1 - (k - 1 - j.val), by omega⟩ : Fin k) = j := Fin.ext (by simp; omega)
  rw [e]

lemma gTail_props (I : Instance k) : ∀ m : ℕ,
    (∀ c, 0 ≤ c → 0 ≤ gTail I m c) ∧ (∀ c, gTail I m c ≤ m * Hs I) ∧
    MonotoneOn (gTail I m) (Set.Ici 0) := by
  intro m
  induction m with
  | zero =>
    refine ⟨fun c _ => by simp [gTail], fun c => by simp [gTail], ?_⟩
    intro a _ b _ _; simp [gTail]
  | succ m ih =>
    by_cases hm : m < k
    · set j : Fin k := ⟨k - 1 - m, by omega⟩ with hj
      have hmj : m = k - 1 - j.val := by simp [hj]; omega
      have e : gTail I (m + 1) = tradeoffValue (I.μ j) (I.lo j) (I.hi j) (gTail I m) := by
        rw [hmj]; exact gTail_succ I j
      obtain ⟨h0, hB, hmono⟩ := ih
      have hBn : 0 ≤ (m : ℝ) * Hs I := mul_nonneg (by positivity) (Hs_nonneg I)
      obtain ⟨v0, vB, vm⟩ := value_props (I.lo_le_hi j) (I.lo_nonneg j) (I.support j) hBn h0 hB hmono
      rw [e]
      refine ⟨v0, fun c => ?_, vm⟩
      have := vB c
      have := hi_le_Hs I j
      push_cast
      linarith
    · have e : gTail I (m + 1) = fun _ => 0 := by rw [gTail, dif_neg hm]
      rw [e]
      refine ⟨fun c _ => le_rfl, fun c => ?_, ?_⟩
      · show (0 : ℝ) ≤ _
        exact mul_nonneg (by positivity) (Hs_nonneg I)
      intro a _ b _ _; exact le_rfl

end SeqMechExPost.Optimal.SMAux


open MeasureTheory

namespace SeqMechExPost.Optimal.SMAux

open SeqMechExPost.Optimal

variable {k : ℕ}

/-- the day-`j` section of an adjusted mechanism at history `h` -/
noncomputable def sec (A : AdjMech k) (j : Fin k) (h : Fin k → ℝ) : StaticMech :=
  ⟨fun t => A.x j (Function.update h j t), fun t => A.pHat j (Function.update h j t)⟩

/-- the partial sum in (15) -/
noncomputable def Rj (A : AdjMech k) (j : Fin k) (v : Fin k → ℝ) : ℝ :=
  ∑ i, (if i.val = 0 then A.pHat i v else if i ≤ j then v i * A.x i v else 0)

lemma contValue_eq (I : Instance k) (A : AdjMech k) (j : Fin k) :
    contValue I A j = ∫ v, (Rj A j v + gNext I j (tu A j v)) ∂I.law := rfl

lemma stageG_pos (I : Instance k) (j : Fin k) (hj : j.val ≠ 0) : stageG I j = gNext I j := by
  unfold stageG gNext; rw [if_neg hj]

lemma gHat_eq_gNext (I : Instance k) (j : Fin k) (hj : j.val ≠ 0) :
    gHat I j = gNext I ⟨j.val - 1, by omega⟩ := by
  unfold gHat
  rw [stageG_pos I j hj]
  unfold gNext
  rw [← gTail_succ I j]
  congr 1
  simp only
  omega

lemma gNext_props (I : Instance k) (j : Fin k) :
    (∀ c, 0 ≤ c → 0 ≤ gNext I j c) ∧ (∀ c, gNext I j c ≤ k * Hs I) ∧
    MonotoneOn (gNext I j) (Set.Ici 0) := by
  obtain ⟨a, b, c⟩ := gTail_props I (k - 1 - j.val)
  refine ⟨a, fun u => le_trans (b u) ?_, c⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : k - 1 - j.val ≤ k)) (Hs_nonneg I)

lemma gHat_mono (I : Instance k) (j : Fin k) (hj : j.val ≠ 0) :
    MonotoneOn (gHat I j) (Set.Ici 0) := by
  rw [gHat_eq_gNext I j hj]; exact (gNext_props I _).2.2

lemma stage_K (I : Instance k) (j : Fin k) :
    ∀ t ∈ Set.Icc (I.lo j) (I.hi j), ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ u, 0 ≤ u →
      t * x + stageG I j u ≤ Hs I + k * Hs I := by
  intro t ht x hx u hu
  have h0 : 0 ≤ t := le_trans (I.lo_nonneg j) ht.1
  have h1 : t * x ≤ Hs I := by nlinarith [ht.2, hx.1, hx.2, hi_le_Hs I j]
  unfold stageG
  split_ifs with hj
  · have := (gTail_props I (k - 1)).2.1 u
    have h2 : ((k - 1 : ℕ) : ℝ) * Hs I ≤ k * Hs I :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : k - 1 ≤ k)) (Hs_nonneg I)
    linarith
  · have := (gNext_props I j).2.1 u
    unfold gNext at this
    linarith

lemma agree_splice_update (j : Fin k) (hj : j.val ≠ 0) (h w : Fin k → ℝ) :
    ∀ l, l ≤ j → splice ⟨j.val - 1, by omega⟩ h w l = Function.update h j (w j) l := by
  intro l hl
  unfold splice
  by_cases hlj : l = j
  · subst hlj
    rw [if_neg (by rw [Fin.le_def]; simp; omega)]
    simp
  · have : l.val < j.val := lt_of_le_of_ne (Fin.le_def.mp hl) (fun e => hlj (Fin.ext e))
    rw [if_pos (by rw [Fin.le_def]; simp; omega), Function.update_of_ne hlj]


lemma int_gclip {ν : Measure ℝ} {lo hi : ℝ} [IsProbabilityMeasure ν]
    (hsupp : ν (Set.Icc lo hi)ᶜ = 0) {g : ℝ → ℝ} {B : ℝ}
    (hg0 : ∀ u, 0 ≤ u → 0 ≤ g u) (hgB : ∀ u, g u ≤ B) (hgm : MonotoneOn g (Set.Ici 0))
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ t ∈ Set.Icc lo hi, 0 ≤ f t) :
    Integrable (fun t => g (f t)) ν := by
  have hmeas : Measurable (fun t => (fun c => g (max c 0)) (f t)) :=
    (monotone_clip hgm).measurable.comp hf
  refine Integrable.of_bound (hmeas.aestronglyMeasurable.congr ?_) (max B 0) ?_
  · filter_upwards [ae_Icc' hsupp] with t ht
    show g (max _ 0) = _
    rw [max_eq_left (hf0 t ht)]
  · filter_upwards [ae_Icc' hsupp] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _ (hf0 t ht))]
    exact le_trans (hgB _) (le_max_left _ _)


section feas

variable {I : Instance k} {A : AdjMech k} (hA : A.AdjFeasible I)
include hA

lemma meas_tu (j : Fin k) : Measurable (tu A j) :=
  ((measurable_pi_apply j).mul (hA.1.2.1 j).1).sub (hA.1.2.1 j).2

lemma tu_nonneg_aux : ∀ n : ℕ, ∀ i : Fin k, i.val + n + 1 = k → ∀ v, I.InBox v →
    0 ≤ tu A i v := by
  intro n
  induction n with
  | zero =>
    intro i hi v hv
    have h : ¬ i.val + 1 < k := by omega
    have := hA.2.2 i v hv
    rw [nextU_last hA i h] at this
    exact this
  | succ n ih =>
    intro i hi v hv
    have h : i.val + 1 < k := by omega
    have := hA.2.2 i v hv
    rw [nextU_eq hA i h] at this
    refine le_trans (integral_nonneg_of_ae ?_) this
    filter_upwards [ae_box I] with w hw
    exact ih ⟨i.val + 1, h⟩ (by simp; omega) _ (splice_box i hv hw)

lemma tu_nonneg (i : Fin k) {v : Fin k → ℝ} (hv : I.InBox v) : 0 ≤ tu A i v :=
  tu_nonneg_aux hA (k - 1 - i.val) i (by have := i.isLt; omega) v hv

lemma tu_splice_update (j : Fin k) (hj : j.val ≠ 0) (h w : Fin k → ℝ) :
    tu A j (splice ⟨j.val - 1, by omega⟩ h w) = tu A j (Function.update h j (w j)) := by
  have hag := agree_splice_update j hj h w
  have e := hA.1.1 j _ _ hag
  unfold tu
  rw [e.1, e.2, hag j le_rfl]

lemma nextU_prev (j : Fin k) (hj : j.val ≠ 0) (h : Fin k → ℝ) :
    A.nextU I ⟨j.val - 1, by omega⟩ h = ∫ t, tu A j (Function.update h j t) ∂I.μ j := by
  have hlt : (⟨j.val - 1, by omega⟩ : Fin k).val + 1 < k := by simp; omega
  rw [nextU_eq hA _ hlt]
  have e : (⟨(⟨j.val - 1, by omega⟩ : Fin k).val + 1, hlt⟩ : Fin k) = j := Fin.ext (by simp; omega)
  rw [e]
  simp_rw [tu_splice_update hA j hj h]
  exact integral_eval I j ((meas_tu hA j).comp (measurable_update h))

lemma sec_meas_x (j : Fin k) (h : Fin k → ℝ) : Measurable (sec A j h).x :=
  (hA.1.2.1 j).1.comp (measurable_update h)

lemma sec_meas_p (j : Fin k) (h : Fin k → ℝ) : Measurable (sec A j h).p :=
  (hA.1.2.1 j).2.comp (measurable_update h)

lemma sec_x01 (j : Fin k) {h : Fin k → ℝ} (hh : I.InBox h) :
    ∀ t ∈ Set.Icc (I.lo j) (I.hi j), (sec A j h).x t ∈ Set.Icc (0 : ℝ) 1 :=
  fun t ht => hA.1.2.2.1 j _ (update_box hh j ht)

lemma sec_IR (j : Fin k) {h : Fin k → ℝ} (hh : I.InBox h) :
    ∀ t ∈ Set.Icc (I.lo j) (I.hi j), 0 ≤ t * (sec A j h).x t - (sec A j h).p t := by
  intro t ht
  have := tu_nonneg hA j (update_box hh j ht)
  unfold tu at this
  simpa [sec] using this

lemma sec_int_p (j : Fin k) {h : Fin k → ℝ} (hh : I.InBox h) :
    Integrable (sec A j h).p (I.μ j) := by
  refine integrable_of_eval I j (sec_meas_p hA j h) ?_
  by_cases hj : j.val = 0
  · refine (hA.1.2.2.2.1 j).congr (Filter.Eventually.of_forall (fun w => ?_))
    have : ∀ l, l ≤ j → w l = Function.update h j (w j) l := by
      intro l hl
      have : l = j := Fin.ext (by have := Fin.le_def.mp hl; omega)
      subst this; simp
    exact (hA.1.1 j _ _ this).2
  · refine (hA.1.2.2.2.2 ⟨j.val - 1, by omega⟩ j h hh).congr
      (Filter.Eventually.of_forall (fun w => ?_))
    exact (hA.1.1 j _ _ (agree_splice_update j hj h w)).2

lemma sec_feasible (j : Fin k) {h : Fin k → ℝ} (hh : I.InBox h) :
    TradeoffFeasible (I.μ j) (I.lo j) (I.hi j) (stageG I j)
      (∫ t, tu A j (Function.update h j t) ∂I.μ j) (sec A j h) := by
  have hmx := sec_meas_x hA j h
  have hmp := sec_meas_p hA j h
  have hx01 := sec_x01 hA j hh
  have hIR := sec_IR hA j hh
  have hp := sec_int_p hA j hh
  have htx := int_tx (I.lo_nonneg j) (I.support j) hmx hx01
  have hu : Measurable (fun t => t * (sec A j h).x t - (sec A j h).p t) :=
    (measurable_id.mul hmx).sub hmp
  refine ⟨hmx, hmp, hx01, ?_, hIR, hp, ?_, ?_⟩
  · intro v hv v' hv'
    have := hA.2.1 j _ (update_box hh j hv) v' hv'
    simpa [sec] using this
  · unfold stageG
    split_ifs with hj
    · obtain ⟨a, b, c⟩ := gTail_props I (k - 1)
      have hg := int_gclip (I.support j) a b c hu hIR
      exact (htx.add (hg.sub (htx.sub hp))).congr
        (Filter.Eventually.of_forall (fun t => by simp only [Pi.add_apply, Pi.sub_apply]; try ring))
    · obtain ⟨a, b, c⟩ := gTail_props I (k - 1 - j.val)
      exact htx.add (int_gclip (I.support j) a b c hu hIR)
  · refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    simp [sec, tu]

lemma sec_obj_le (j : Fin k) {h : Fin k → ℝ} (hh : I.InBox h) :
    tradeoffObj (I.μ j) (stageG I j) (sec A j h)
      ≤ gHat I j (∫ t, tu A j (Function.update h j t) ∂I.μ j) :=
  le_value (I.support j) (stage_K I j) (sec_feasible hA j hh)

lemma cH_nonneg (j : Fin k) {h : Fin k → ℝ} (hh : I.InBox h) :
    0 ≤ ∫ t, tu A j (Function.update h j t) ∂I.μ j := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [ae_Icc I j] with t ht
  exact tu_nonneg hA j (update_box hh j ht)

/-- the key per-history inequality of the backward induction, for days `j ≥ 1` -/
lemma step_le (j : Fin k) (hj : j.val ≠ 0) {h : Fin k → ℝ} (hh : I.InBox h) :
    ∫ t, (t * A.x j (Function.update h j t) + gNext I j (tu A j (Function.update h j t))) ∂I.μ j
      ≤ gNext I ⟨j.val - 1, by omega⟩ (tu A ⟨j.val - 1, by omega⟩ h) := by
  have e1 : ∫ t, (t * A.x j (Function.update h j t) + gNext I j (tu A j (Function.update h j t)))
      ∂I.μ j = tradeoffObj (I.μ j) (stageG I j) (sec A j h) := by
    unfold tradeoffObj
    rw [stageG_pos I j hj]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    simp [sec, tu]
  rw [e1, ← gHat_eq_gNext I j hj]
  refine le_trans (sec_obj_le hA j hh) ?_
  refine gHat_mono I j hj (cH_nonneg hA j hh) (tu_nonneg hA _ hh) ?_
  have := hA.2.2 ⟨j.val - 1, by omega⟩ h hh
  rw [nextU_prev hA j hj h] at this
  exact this

lemma step0_le (i0 : Fin k) (hi0 : i0.val = 0) {c0 : ℝ}
    (hc0 : ∀ c, 0 ≤ c → gHat I i0 c ≤ gHat I i0 c0) {h : Fin k → ℝ} (hh : I.InBox h) :
    ∫ t, (A.pHat i0 (Function.update h i0 t) + gNext I i0 (tu A i0 (Function.update h i0 t)))
      ∂I.μ i0 ≤ gHat I i0 c0 := by
  have e1 : ∫ t, (A.pHat i0 (Function.update h i0 t)
      + gNext I i0 (tu A i0 (Function.update h i0 t))) ∂I.μ i0
      = tradeoffObj (I.μ i0) (stageG I i0) (sec A i0 h) := by
    unfold tradeoffObj stageG
    rw [if_pos hi0]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    have e2 : gTail I (k - 1) = gNext I i0 := by unfold gNext; rw [hi0]; rfl
    simp only [sec, tu, Function.update_self, e2]
    ring
  rw [e1]
  exact le_trans (sec_obj_le hA i0 hh) (hc0 _ (cH_nonneg hA i0 hh))

end feas

end SeqMechExPost.Optimal.SMAux


open MeasureTheory

namespace SeqMechExPost.Optimal.SMAux

open SeqMechExPost.Optimal

variable {k : ℕ}

section chain

variable {I : Instance k} {A : AdjMech k} (hA : A.AdjFeasible I)
include hA

lemma int_vxA (j : Fin k) : Integrable (fun v => v j * A.x j v) I.law :=
  integrable_of_box_bound I ((measurable_pi_apply j).mul (hA.1.2.1 j).1) (I.hi j)
    (fun v hv => abs_mul_x_le I (hv j) (hA.1.2.2.1 j v hv))

lemma int_Rj (j : Fin k) : Integrable (Rj A j) I.law := by
  unfold Rj
  refine integrable_finsetSum _ (fun i _ => ?_)
  by_cases h1 : i.val = 0
  · simp only [h1, if_true]; exact hA.1.2.2.2.1 i
  · by_cases h2 : i ≤ j
    · simp only [h1, h2, if_true, if_false]; exact int_vxA hA i
    · simp only [h1, h2, if_false]; exact integrable_const _

lemma int_gnext_tu (j j' : Fin k) : Integrable (fun v => gNext I j (tu A j' v)) I.law := by
  obtain ⟨hg0, hgB, hgm⟩ := gNext_props I j
  have hmeas : Measurable (fun v => (fun c => gNext I j (max c 0)) (tu A j' v)) :=
    (monotone_clip hgm).measurable.comp (meas_tu hA j')
  refine Integrable.of_bound (hmeas.aestronglyMeasurable.congr ?_) (max (k * Hs I) 0) ?_
  · filter_upwards [ae_box I] with v hv
    show gNext I j (max _ 0) = _
    rw [max_eq_left (tu_nonneg hA j' hv)]
  · filter_upwards [ae_box I] with v hv
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 _ (tu_nonneg hA j' hv))]
    exact le_trans (hgB _) (le_max_left _ _)

lemma Rj_step (j : Fin k) (hj : j.val ≠ 0) (v : Fin k → ℝ) :
    Rj A j v = Rj A ⟨j.val - 1, by omega⟩ v + v j * A.x j v := by
  unfold Rj
  have e : ∀ i : Fin k, (if i.val = 0 then A.pHat i v else if i ≤ j then v i * A.x i v else 0)
      = (if i.val = 0 then A.pHat i v else if i ≤ ⟨j.val - 1, by omega⟩ then v i * A.x i v else 0)
        + (if i = j then v i * A.x i v else 0) := by
    intro i
    by_cases h1 : i.val = 0
    · have : i ≠ j := fun e => hj (e ▸ h1)
      simp [h1, this]
    · by_cases h3 : i = j
      · subst h3
        have : ¬ i ≤ (⟨i.val - 1, by omega⟩ : Fin k) := by rw [Fin.le_def]; simp; omega
        simp [h1, this]
      · have : (i ≤ j) ↔ (i ≤ (⟨j.val - 1, by omega⟩ : Fin k)) := by
          rw [Fin.le_def, Fin.le_def]
          have : i.val ≠ j.val := fun e => h3 (Fin.ext e)
          simp; omega
        simp only [h1, h3, if_false, this, add_zero]
  rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma Rj_base (i0 : Fin k) (hi0 : i0.val = 0) (v : Fin k → ℝ) : Rj A i0 v = A.pHat i0 v := by
  unfold Rj
  rw [Finset.sum_eq_single i0]
  · simp [hi0]
  · intro i _ hne
    have : i.val ≠ 0 := fun e => hne (Fin.ext (by rw [e, hi0]))
    have h2 : ¬ i ≤ i0 := by rw [Fin.le_def]; omega
    simp [this, h2]
  · simp

lemma cont_split (j : Fin k) (hj : j.val ≠ 0) :
    contValue I A j = ∫ v, Rj A ⟨j.val - 1, by omega⟩ v ∂I.law
      + ∫ v, (∫ t, (t * A.x j (Function.update v j t)
          + gNext I j (tu A j (Function.update v j t))) ∂I.μ j) ∂I.law ∧
    Integrable (fun v => ∫ t, (t * A.x j (Function.update v j t)
          + gNext I j (tu A j (Function.update v j t))) ∂I.μ j) I.law := by
  have hΦ : Integrable (fun v => v j * A.x j v + gNext I j (tu A j v)) I.law :=
    (int_vxA hA j).add (int_gnext_tu hA j j)
  have e : ∀ v t, (fun v => v j * A.x j v + gNext I j (tu A j v)) (Function.update v j t)
      = t * A.x j (Function.update v j t) + gNext I j (tu A j (Function.update v j t)) := by
    intro v t; simp
  have h1 := integral_integral_update I j hΦ
  have h2 := integrable_integral_update I j hΦ
  simp_rw [e] at h1 h2
  refine ⟨?_, h2⟩
  rw [contValue_eq, h1, ← integral_add (int_Rj hA _) hΦ]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only
  rw [Rj_step hA j hj v]
  ring

lemma cont_step_le (j : Fin k) (hj : j.val ≠ 0) :
    contValue I A j ≤ contValue I A ⟨j.val - 1, by omega⟩ := by
  obtain ⟨e, hint⟩ := cont_split hA j hj
  rw [e, contValue_eq, integral_add (int_Rj hA _) (int_gnext_tu hA _ _)]
  refine add_le_add le_rfl (integral_mono_ae hint (int_gnext_tu hA _ _) ?_)
  filter_upwards [ae_box I] with v hv
  exact step_le hA j hj hv

lemma cont_step_eq (j : Fin k) (hj : j.val ≠ 0)
    (heq : ∀ h, I.InBox h → ∫ t, (t * A.x j (Function.update h j t)
        + gNext I j (tu A j (Function.update h j t))) ∂I.μ j
      = gNext I ⟨j.val - 1, by omega⟩ (tu A ⟨j.val - 1, by omega⟩ h)) :
    contValue I A j = contValue I A ⟨j.val - 1, by omega⟩ := by
  obtain ⟨e, hint⟩ := cont_split hA j hj
  rw [e, contValue_eq, integral_add (int_Rj hA _) (int_gnext_tu hA _ _)]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_box I] with v hv
  exact heq v hv

lemma cont_base (i0 : Fin k) (hi0 : i0.val = 0) :
    contValue I A i0 = ∫ v, (∫ t, (A.pHat i0 (Function.update v i0 t)
          + gNext I i0 (tu A i0 (Function.update v i0 t))) ∂I.μ i0) ∂I.law ∧
    Integrable (fun v => ∫ t, (A.pHat i0 (Function.update v i0 t)
          + gNext I i0 (tu A i0 (Function.update v i0 t))) ∂I.μ i0) I.law := by
  have hΦ : Integrable (fun v => A.pHat i0 v + gNext I i0 (tu A i0 v)) I.law :=
    (hA.1.2.2.2.1 i0).add (int_gnext_tu hA i0 i0)
  refine ⟨?_, integrable_integral_update I i0 hΦ⟩
  rw [integral_integral_update I i0 hΦ, contValue_eq]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only
  rw [Rj_base hA i0 hi0 v]

lemma cont_top (j : Fin k) (hj : j.val + 1 = k) : contValue I A j = A.adjObj I := by
  rw [contValue_eq]
  unfold AdjMech.adjObj Rj
  have hg : ∀ u, gNext I j u = 0 := by
    intro u; unfold gNext
    rw [show k - 1 - j.val = 0 by omega]; rfl
  refine integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only [hg, add_zero]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : i ≤ j := by rw [Fin.le_def]; have := i.isLt; omega
  simp [this]

end chain

end SeqMechExPost.Optimal.SMAux


open MeasureTheory

namespace SeqMechExPost.Optimal.SMAux

open SeqMechExPost.Optimal

variable {k : ℕ}

section thm7

variable {I : Instance k} {X P : Fin k → ℝ → ℝ → ℝ}
  (hopt : ∀ i c, 0 ≤ c → IsOptimizer I i c ⟨X i c, P i c⟩)
  (hmeas : ∀ i, Measurable (Function.uncurry (X i)) ∧ Measurable (Function.uncurry (P i)))
  {c0 : ℝ} (hc0 : 0 ≤ c0)

lemma tu_thm7 (i : Fin k) (v : Fin k → ℝ) :
    tu (thm7Adj X P c0) i v = cState X P c0 (i.val + 1) v := by
  rw [cState_succ]; rfl

include hopt hmeas hc0 in
lemma nextU_thm7 (i : Fin k) (h : i.val + 1 < k) {v : Fin k → ℝ} (hv : I.InBox v) :
    (thm7Adj X P c0).nextU I i v = cState X P c0 (i.val + 1) v := by
  unfold AdjMech.nextU
  rw [dif_pos h]
  set j : Fin k := ⟨i.val + 1, h⟩ with hj
  set c := cState X P c0 (i.val + 1) v with hc
  have hcn : 0 ≤ c := cState_nonneg X P hopt c0 hc0 v hv _
  have hdep : ∀ w, cState X P c0 (i.val + 1) (splice i v w) = c := by
    intro w
    refine cState_dep X P c0 _ _ _ (fun l hl => ?_)
    unfold splice
    rw [if_pos (Fin.le_def.mpr (by omega))]
  have hsj : ∀ w, splice i v w j = w j := by
    intro w; unfold splice
    rw [if_neg (by rw [Fin.le_def]; simp [hj])]
  have e1 : ∀ w, (splice i v w j * (thm7Adj X P c0).x j (splice i v w)
      - (thm7Adj X P c0).pHat j (splice i v w))
      = (fun t => t * X j c t - P j c t) (w j) := by
    intro w
    show splice i v w j * X j (cState X P c0 (i.val + 1) (splice i v w)) (splice i v w j)
      - P j (cState X P c0 (i.val + 1) (splice i v w)) (splice i v w j) = _
    rw [hdep, hsj]
  simp_rw [e1]
  have hgm : Measurable (fun t => t * X j c t - P j c t) := by
    have h1 : Measurable (fun t => X j c t) :=
      (hmeas j).1.comp (measurable_const.prodMk measurable_id)
    have h2 : Measurable (fun t => P j c t) :=
      (hmeas j).2.comp (measurable_const.prodMk measurable_id)
    exact (measurable_id.mul h1).sub h2
  rw [integral_eval I j hgm]
  exact (hopt j c hcn).1.2.2.2.2.2.2.2

include hopt hc0 in
lemma P_bound (i : Fin k) {v : Fin k → ℝ} (hv : I.InBox v) :
    |P i (cState X P c0 i.val v) (v i)| ≤ Hs I + c0 + (k + 1) * Dw I := by
  have hc := cState_nonneg X P hopt c0 hc0 v hv i.val
  have hcle := cState_le X P hopt c0 hc0 v hv i.val
  have hfe := (hopt i _ hc).1
  have hb := static_bounds (I.lo_le_hi i) (I.lo_nonneg i) (I.support i) hfe (v i) (hv i)
  have hx := hfe.2.2.1 (v i) (hv i)
  simp only at hb hx
  have h0 : 0 ≤ v i := le_trans (I.lo_nonneg i) (hv i).1
  have htx : v i * X i (cState X P c0 i.val v) (v i) ≤ Hs I := by
    nlinarith [(hv i).2, hx.1, hx.2, hi_le_Hs I i]
  have htx0 : 0 ≤ v i * X i (cState X P c0 i.val v) (v i) := mul_nonneg h0 hx.1
  have hgap := gap_le_Dw I i
  have hD := Dw_nonneg I
  have hik : (i.val : ℝ) * Dw I ≤ k * Dw I :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast i.isLt.le) hD
  rw [abs_le]
  constructor <;> nlinarith [Hs_nonneg I]

include hopt hmeas hc0 in
lemma thm7_feasible : (thm7Adj X P c0).AdjFeasible I := by
  have hcm := cState_meas X P hmeas c0
  have hxm : ∀ i : Fin k, Measurable (fun v : Fin k → ℝ => X i (cState X P c0 i.val v) (v i)) :=
    fun i => meas_comp _ (hmeas i).1 (hcm i.val) (measurable_pi_apply i)
  have hpm : ∀ i : Fin k, Measurable (fun v : Fin k → ℝ => P i (cState X P c0 i.val v) (v i)) :=
    fun i => meas_comp _ (hmeas i).2 (hcm i.val) (measurable_pi_apply i)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i v w h
    have hc : cState X P c0 i.val v = cState X P c0 i.val w :=
      cState_dep X P c0 _ v w (fun j hj => h j (le_of_lt (Fin.lt_def.mpr hj)))
    have hvi : v i = w i := h i le_rfl
    show X i (cState X P c0 i.val v) (v i) = X i (cState X P c0 i.val w) (w i) ∧
      P i (cState X P c0 i.val v) (v i) = P i (cState X P c0 i.val w) (w i)
    rw [hc, hvi]
    exact ⟨rfl, rfl⟩
  · intro i; exact ⟨hxm i, hpm i⟩
  · intro i v hv
    exact (hopt i _ (cState_nonneg X P hopt c0 hc0 v hv i.val)).1.2.2.1 (v i) (hv i)
  · intro i
    exact integrable_of_box_bound I (hpm i) _ (fun v hv => P_bound hopt hc0 i hv)
  · intro i j v hv
    have hs : Measurable (fun w : Fin k → ℝ => splice i v w) :=
      (measurable_splice i).comp (measurable_const.prodMk measurable_id)
    exact integrable_of_box_bound I ((hpm j).comp hs) _
      (fun w hw => P_bound hopt hc0 j (splice_box i hv hw))
  · intro i v hv a ha
    have hc : cState X P c0 i.val (Function.update v i a) = cState X P c0 i.val v :=
      cState_dep X P c0 _ _ _ (fun j hj => by
        rw [Function.update_of_ne (fun e => by subst e; simp at hj)])
    show v i * X i (cState X P c0 i.val (Function.update v i a)) ((Function.update v i a) i)
        - P i (cState X P c0 i.val (Function.update v i a)) ((Function.update v i a) i)
      ≤ v i * X i (cState X P c0 i.val v) (v i) - P i (cState X P c0 i.val v) (v i)
    rw [hc, Function.update_self]
    exact (hopt i _ (cState_nonneg X P hopt c0 hc0 v hv i.val)).1.2.2.2.1 (v i) (hv i) a ha
  · intro i v hv
    by_cases h : i.val + 1 < k
    · rw [nextU_thm7 hopt hmeas hc0 i h hv]
      exact le_of_eq (tu_thm7 i v).symm
    · unfold AdjMech.nextU; rw [dif_neg h]
      have := cState_nonneg X P hopt c0 hc0 v hv (i.val + 1)
      rw [← tu_thm7 i v] at this
      exact this

lemma sec_thm7 (j : Fin k) (h : Fin k → ℝ) (t : ℝ) :
    (thm7Adj X P c0).x j (Function.update h j t) = X j (cState X P c0 j.val h) t ∧
    (thm7Adj X P c0).pHat j (Function.update h j t) = P j (cState X P c0 j.val h) t := by
  have hc : cState X P c0 j.val (Function.update h j t) = cState X P c0 j.val h :=
    cState_dep X P c0 _ _ _ (fun l hl => by
      rw [Function.update_of_ne (fun e => by subst e; simp at hl)])
  show X j (cState X P c0 j.val (Function.update h j t)) ((Function.update h j t) j) = _ ∧
    P j (cState X P c0 j.val (Function.update h j t)) ((Function.update h j t) j) = _
  rw [hc, Function.update_self]
  exact ⟨rfl, rfl⟩

include hopt hc0 in
lemma step_eq_thm7 (j : Fin k) (hj : j.val ≠ 0) (h : Fin k → ℝ) (hh : I.InBox h) :
    ∫ t, (t * (thm7Adj X P c0).x j (Function.update h j t)
        + gNext I j (tu (thm7Adj X P c0) j (Function.update h j t))) ∂I.μ j
      = gNext I ⟨j.val - 1, by omega⟩ (tu (thm7Adj X P c0) ⟨j.val - 1, by omega⟩ h) := by
  set c := cState X P c0 j.val h with hcdef
  have hc := cState_nonneg X P hopt c0 hc0 h hh j.val
  have e1 : ∫ t, (t * (thm7Adj X P c0).x j (Function.update h j t)
        + gNext I j (tu (thm7Adj X P c0) j (Function.update h j t))) ∂I.μ j
      = tradeoffObj (I.μ j) (stageG I j) ⟨X j c, P j c⟩ := by
    unfold tradeoffObj
    rw [stageG_pos I j hj]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    have := sec_thm7 (X := X) (P := P) (c0 := c0) j h t
    simp only [tu, Function.update_self, this.1, this.2]
    rfl
  rw [e1, (hopt j c hc).2, gHat_eq_gNext I j hj, tu_thm7]
  congr 1
  simp only [hcdef]
  congr 1
  omega

include hopt hc0 in
lemma step0_eq_thm7 (i0 : Fin k) (hi0 : i0.val = 0) (h : Fin k → ℝ) :
    ∫ t, ((thm7Adj X P c0).pHat i0 (Function.update h i0 t)
        + gNext I i0 (tu (thm7Adj X P c0) i0 (Function.update h i0 t))) ∂I.μ i0
      = gHat I i0 c0 := by
  have hc : cState X P c0 i0.val h = c0 := by rw [hi0]; rfl
  have e1 : ∫ t, ((thm7Adj X P c0).pHat i0 (Function.update h i0 t)
        + gNext I i0 (tu (thm7Adj X P c0) i0 (Function.update h i0 t))) ∂I.μ i0
      = tradeoffObj (I.μ i0) (stageG I i0) ⟨X i0 c0, P i0 c0⟩ := by
    unfold tradeoffObj stageG
    rw [if_pos hi0]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun t => ?_))
    have := sec_thm7 (X := X) (P := P) (c0 := c0) i0 h t
    have e2 : gTail I (k - 1) = gNext I i0 := by unfold gNext; rw [hi0]; rfl
    simp only [tu, Function.update_self, this.1, this.2, hc, e2]
    ring
  rw [e1, (hopt i0 c0 hc0).2]

end thm7

theorem lemma6_main {k : ℕ} (I : Instance k) (hk : 0 < k)
    (X P : Fin k → ℝ → ℝ → ℝ)
    (hopt : ∀ i c, 0 ≤ c → IsOptimizer I i c ⟨X i c, P i c⟩)
    (hmeas : ∀ i, Measurable (Function.uncurry (X i)) ∧ Measurable (Function.uncurry (P i)))
    (c0 : ℝ) (hc0 : 0 ≤ c0 ∧ ∀ c, 0 ≤ c → gHat I ⟨0, hk⟩ c ≤ gHat I ⟨0, hk⟩ c0) :
    (thm7Adj X P c0).AdjOptimal I := by
  set i0 : Fin k := ⟨0, hk⟩ with hi0
  have hA := thm7_feasible hopt hmeas hc0.1
  -- the value of the Theorem 7 mechanism
  have hval : ∀ n, ∀ j : Fin k, j.val = n → contValue I (thm7Adj X P c0) j = gHat I i0 c0 := by
    intro n
    induction n with
    | zero =>
      intro j hj
      have : j = i0 := Fin.ext (by simp [hi0, hj])
      subst this
      rw [(cont_base hA i0 rfl).1]
      have : ∀ v, ∫ t, ((thm7Adj X P c0).pHat i0 (Function.update v i0 t)
          + gNext I i0 (tu (thm7Adj X P c0) i0 (Function.update v i0 t))) ∂I.μ i0
          = gHat I i0 c0 := fun v => step0_eq_thm7 hopt hc0.1 i0 rfl v
      simp_rw [this]
      simp
    | succ n ih =>
      intro j hj
      have hj0 : j.val ≠ 0 := by omega
      rw [cont_step_eq hA j hj0 (fun h hh => step_eq_thm7 hopt hc0.1 j hj0 h hh)]
      exact ih _ (by simp; omega)
  have hbound : ∀ A' : AdjMech k, A'.AdjFeasible I →
      ∀ n, ∀ j : Fin k, j.val = n → contValue I A' j ≤ gHat I i0 c0 := by
    intro A' hA' n
    induction n with
    | zero =>
      intro j hj
      have : j = i0 := Fin.ext (by simp [hi0, hj])
      subst this
      obtain ⟨e, hint⟩ := cont_base hA' i0 rfl
      rw [e]
      have : ∫ _v, gHat I i0 c0 ∂I.law = gHat I i0 c0 := by simp
      rw [← this]
      refine integral_mono_ae hint (integrable_const _) ?_
      filter_upwards [ae_box I] with v hv
      exact step0_le hA' i0 rfl hc0.2 hv
    | succ n ih =>
      intro j hj
      have hj0 : j.val ≠ 0 := by omega
      exact le_trans (cont_step_le hA' j hj0) (ih _ (by simp; omega))
  set last : Fin k := ⟨k - 1, by omega⟩ with hlast
  refine ⟨hA, fun A' hA' => ?_⟩
  rw [← cont_top hA' last (by simp [hlast]; omega), ← cont_top hA last (by simp [hlast]; omega),
    hval _ last rfl]
  exact hbound A' hA' _ last rfl

end SeqMechExPost.Optimal.SMAux


open SeqMechExPost.Optimal

theorem solution {k : ℕ} (I : Instance k) (hk : 0 < k)
    (X P : Fin k → ℝ → ℝ → ℝ)
    (hopt : ∀ i c, 0 ≤ c → IsOptimizer I i c ⟨X i c, P i c⟩)
    (hmeas : ∀ i, Measurable (Function.uncurry (X i)) ∧ Measurable (Function.uncurry (P i)))
    (c0 : ℝ) (hc0 : 0 ≤ c0 ∧ ∀ c, 0 ≤ c → gHat I ⟨0, hk⟩ c ≤ gHat I ⟨0, hk⟩ c0) :
    (thm7Adj X P c0).AdjOptimal I :=
  SeqMechExPost.Optimal.SMAux.lemma6_main I hk X P hopt hmeas c0 hc0
