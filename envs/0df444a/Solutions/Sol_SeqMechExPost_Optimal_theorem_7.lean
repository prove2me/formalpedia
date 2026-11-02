-- Prove2me | solution 1 for SeqMechExPost.Optimal.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T11:47:30.052963+00:00
-- url     : https://prove2.me/submissions/6d0ace72-0c68-49a0-a21e-8b79ed01ba71

import Mathlib
import Definitions.Def_SeqMechExPost_Optimal_Model
import Definitions.Def_SeqMechExPost_Optimal_Tradeoff
import Theorems.Thm_SeqMechExPost_Optimal_lemma_3
import Theorems.Thm_SeqMechExPost_Optimal_lemma_6

open MeasureTheory

namespace SeqMechExPost.Optimal.Thm7Aux

open SeqMechExPost.Optimal

variable {k : ℕ}

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
      have := cState_succ X P c0 ⟨n, hn⟩ v
      have := cState_succ X P c0 ⟨n, hn⟩ w
      simp only at *
      rw [cState_succ X P c0 ⟨n, hn⟩ v, cState_succ X P c0 ⟨n, hn⟩ w, h', h ⟨n, hn⟩ (by simp)]
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

lemma key (I : Instance k) (X P : Fin k → ℝ → ℝ → ℝ)
    (hopt : ∀ i c, 0 ≤ c → IsOptimizer I i c ⟨X i c, P i c⟩)
    (hmeas : ∀ i, Measurable (Function.uncurry (X i)) ∧ Measurable (Function.uncurry (P i)))
    (c0 : ℝ) (hc0 : 0 ≤ c0) (v : Fin k → ℝ) (hv : I.InBox v) (i : Fin k) :
    (thm7Mech X P c0).p i v = (unadjust I (thm7Adj X P c0)).p i v := by
  show (if i.val + 1 < k then v i * X i (cState X P c0 i.val v) (v i)
    else P i (cState X P c0 i.val v) (v i))
      = P i (cState X P c0 i.val v) (v i) + (thm7Adj X P c0).nextU I i v
  unfold AdjMech.nextU
  split_ifs with h
  · set j : Fin k := ⟨i.val + 1, h⟩ with hj
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
    have hint : ∫ w, (splice i v w j * (thm7Adj X P c0).x j (splice i v w)
        - (thm7Adj X P c0).pHat j (splice i v w)) ∂I.law = c := by
      have e1 : ∀ w, (splice i v w j * (thm7Adj X P c0).x j (splice i v w)
          - (thm7Adj X P c0).pHat j (splice i v w))
          = (fun t => t * X j c t - P j c t) (w j) := by
        intro w
        show splice i v w j * X j (cState X P c0 (i.val + 1) (splice i v w)) (splice i v w j)
          - P j (cState X P c0 (i.val + 1) (splice i v w)) (splice i v w j) = _
        rw [hdep, hsj]
      simp_rw [e1]
      have hmp := measurePreserving_eval I.μ j
      have hgm : Measurable (fun t => t * X j c t - P j c t) := by
        have h1 : Measurable (fun t => X j c t) :=
          (hmeas j).1.comp (measurable_const.prodMk measurable_id)
        have h2 : Measurable (fun t => P j c t) :=
          (hmeas j).2.comp (measurable_const.prodMk measurable_id)
        exact (measurable_id.mul h1).sub h2
      unfold Instance.law
      rw [← integral_map hmp.measurable.aemeasurable hgm.aestronglyMeasurable, hmp.map_eq]
      exact (hopt j c hcn).1.2.2.2.2.2.2.2
    rw [hint, hc, cState_succ X P c0 i v]
    ring
  · simp

end SeqMechExPost.Optimal.Thm7Aux

open SeqMechExPost.Optimal SeqMechExPost.Optimal.Thm7Aux

theorem solution {k : ℕ} (I : Instance k) (hk : 0 < k)
    (X P : Fin k → ℝ → ℝ → ℝ)
    (hopt : ∀ i c, 0 ≤ c → IsOptimizer I i c ⟨X i c, P i c⟩)
    (hmeas : ∀ i, Measurable (Function.uncurry (X i)) ∧ Measurable (Function.uncurry (P i)))
    (c0 : ℝ) (hc0 : 0 ≤ c0 ∧ ∀ c, 0 ≤ c → gHat I ⟨0, hk⟩ c ≤ gHat I ⟨0, hk⟩ c0) :
    (thm7Mech X P c0).IsOptimal I := by
  have h6 := lemma_6 I hk X P hopt hmeas c0 hc0
  have h3 := lemma_3 I
  set A := thm7Adj X P c0 with hA
  set N := unadjust I A with hN
  set M := thm7Mech X P c0 with hM
  have hNF : N.Feasible I := (h3.2 A h6.1).1
  have hpre : ∀ i v, I.InBox v → (adjust I N).pHat i v = A.pHat i v := (h3.2 A h6.1).2
  have heqp : ∀ i v, I.InBox v → M.p i v = N.p i v :=
    fun i v hv => key I X P hopt hmeas c0 hc0.1 v hv i
  have hU : ∀ i v, I.InBox v → M.U I i v = N.U I i v := by
    intro i v hv
    unfold SeqMech.U
    refine integral_congr_ae ?_
    filter_upwards [ae_box I] with w hw
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [heqp j _ (splice_box i hv hw)]
    rfl
  have hMF : M.Feasible I := by
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro i v w h
      have hc : cState X P c0 i.val v = cState X P c0 i.val w :=
        cState_dep X P c0 _ v w (fun j hj => h j (le_of_lt (Fin.lt_def.mpr hj)))
      have hvi : v i = w i := h i le_rfl
      show X i (cState X P c0 i.val v) (v i) = X i (cState X P c0 i.val w) (w i) ∧
        (if i.val + 1 < k then v i * X i (cState X P c0 i.val v) (v i)
          else P i (cState X P c0 i.val v) (v i)) =
        (if i.val + 1 < k then w i * X i (cState X P c0 i.val w) (w i)
          else P i (cState X P c0 i.val w) (w i))
      rw [hc, hvi]
      exact ⟨rfl, rfl⟩
    · intro i
      have hc := cState_meas X P hmeas c0 i.val
      have hx : Measurable (fun v : Fin k → ℝ => X i (cState X P c0 i.val v) (v i)) :=
        meas_comp _ (hmeas i).1 hc (measurable_pi_apply i)
      refine ⟨hx, ?_⟩
      show Measurable (fun v : Fin k → ℝ => if i.val + 1 < k then v i * X i (cState X P c0 i.val v) (v i)
          else P i (cState X P c0 i.val v) (v i))
      split_ifs
      · exact (measurable_pi_apply i).mul hx
      · exact meas_comp _ (hmeas i).2 hc (measurable_pi_apply i)
    · exact hNF.1.2.2.1
    · intro i
      refine (hNF.1.2.2.2.1 i).congr ?_
      filter_upwards [ae_box I] with v hv
      exact (heqp i v hv).symm
    · intro i j v hv
      refine (hNF.1.2.2.2.2 i j v hv).congr ?_
      filter_upwards [ae_box I] with w hw
      exact (heqp j _ (splice_box i hv hw)).symm
    · intro i v hv a ha
      have hb := update_box hv i ha
      rw [heqp i _ hb, heqp i v hv, hU i _ hb, hU i v hv]
      exact hNF.2.1 i v hv a ha
    · intro i v hv
      rw [heqp i v hv]
      exact hNF.2.2 i v hv
  have hrevMN : M.revenue I = N.revenue I := by
    unfold SeqMech.revenue
    refine integral_congr_ae ?_
    filter_upwards [ae_box I] with v hv
    exact Finset.sum_congr rfl (fun i _ => heqp i v hv)
  have hrevN : N.revenue I = (adjust I N).adjObj I := ((h3.1 N hNF.1).2.1)
  have hadj : (adjust I N).adjObj I = A.adjObj I := by
    unfold AdjMech.adjObj
    refine integral_congr_ae ?_
    filter_upwards [ae_box I] with v hv
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs
    · exact hpre i v hv
    · rfl
  refine ⟨hMF, fun M' hM' => ?_⟩
  have h3' := h3.1 M' hM'.1
  rw [h3'.2.1, hrevMN, hrevN, hadj]
  exact h6.2 _ (h3'.1.mp hM')
