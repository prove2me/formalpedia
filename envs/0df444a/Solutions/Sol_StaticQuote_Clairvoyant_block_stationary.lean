-- Prove2me | solution 1 for StaticQuote.Clairvoyant.block_stationary
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T15:03:23.23627+00:00
-- url     : https://prove2.me/submissions/197018c1-9ac9-4e87-a0e8-6d057af1c4f7

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting

open MeasureTheory Filter
open scoped ENNReal
open StaticQuote.Clairvoyant

namespace SQCBlockAux

open ProbabilityTheory

set_option linter.unusedSectionVars false
variable {Ω : Type*} [MeasurableSpace Ω]

/-- the model seen from customer `s`: customer `m` of the shifted model is customer `s + m`. -/
def shift (Q : Model Ω) (s : ℕ) : Model Ω :=
  ⟨fun k => Q.T (s + k), fun k => Q.x (s + k), Q.δ, Q.ce, Q.cd⟩

lemma sum_Icc_shift (s N : ℕ) (f : ℕ → ℝ≥0∞) :
    ∑ n ∈ Finset.Icc (s + 1) (s + N), f n = ∑ m ∈ Finset.Icc 1 N, f (s + m) := by
  rw [← Finset.map_add_left_Icc, Finset.sum_map]
  rfl

lemma arrival_add (Q : Model Ω) (s m : ℕ) (ω : Ω) :
    Q.arrival (s + m) ω = Q.arrival s ω + (shift Q s).arrival m ω := by
  induction m with
  | zero => simp [Model.arrival]
  | succ m ih =>
    unfold Model.arrival at *
    rw [← add_assoc, Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega), ih]
    simp only [shift]
    ring

lemma gamma_shift (Q : Model Ω) (s N : ℕ) (ω : Ω) :
    Q.gamma (s + 1) (s + N) ω = (shift Q s).gamma 1 N ω := by
  set A := Q.arrival s ω
  apply le_antisymm
  · unfold Model.gamma
    refine le_iInf₂ fun y' hy' => ?_
    refine (iInf₂_le (fun n => y' (n - s) + A) ⟨fun n hn => ?_, fun n hn => ?_⟩).trans_eq ?_
    · rw [sum_Icc_shift]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [Model.due, arrival_add, Nat.add_sub_cancel_left, shift]
      congr 2
      ring
    · simp only [Finset.mem_Icc] at hn
      obtain ⟨m, rfl⟩ : ∃ m, n = s + m := ⟨n - s, by omega⟩
      have := hy'.1 m (by simp only [Finset.mem_Icc]; omega)
      simp only [Nat.add_sub_cancel_left, arrival_add]
      linarith
    · simp only [Finset.mem_Ico] at hn
      obtain ⟨m, rfl⟩ : ∃ m, n = s + m := ⟨n - s, by omega⟩
      have := hy'.2 m (by simp only [Finset.mem_Ico]; omega)
      simp only [shift] at this
      have h2 : s + m + 1 - s = m + 1 := by omega
      simp only [Nat.add_sub_cancel_left, h2]
      linarith
  · unfold Model.gamma
    refine le_iInf₂ fun y hy => ?_
    refine (iInf₂_le (fun m => y (s + m) - A) ⟨fun m hm => ?_, fun m hm => ?_⟩).trans_eq ?_
    · rw [sum_Icc_shift]
      refine Finset.sum_congr rfl fun m _ => ?_
      simp only [Model.due, arrival_add, shift]
      congr 2
      ring
    · simp only [Finset.mem_Icc] at hm
      have := hy.1 (s + m) (by simp only [Finset.mem_Icc]; omega)
      rw [arrival_add] at this
      simp only
      linarith
    · simp only [Finset.mem_Ico] at hm
      have := hy.2 (s + m) (by simp only [Finset.mem_Ico]; omega)
      simp only [shift, ← add_assoc]
      linarith

lemma gamma_le_of_agree {Ω' : Type*} [MeasurableSpace Ω'] (Q : Model Ω) (Q' : Model Ω')
    (ω : Ω) (ω' : Ω') (N : ℕ) (hδ : Q.δ = Q'.δ) (hce : Q.ce = Q'.ce) (hcd : Q.cd = Q'.cd)
    (hT : ∀ k, 1 ≤ k → k ≤ N → Q.T k ω = Q'.T k ω')
    (hx : ∀ k, 1 ≤ k → k ≤ N → Q.x k ω = Q'.x k ω') :
    Q'.gamma 1 N ω' ≤ Q.gamma 1 N ω := by
  have ha : ∀ n, n ≤ N → Q.arrival n ω = Q'.arrival n ω' := by
    intro n hn
    unfold Model.arrival
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    exact hT k hk.1 (by omega)
  unfold Model.gamma
  refine le_iInf₂ fun y hy => ?_
  refine (iInf₂_le y ⟨fun n hn => ?_, fun n hn => ?_⟩).trans_eq ?_
  · refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    simp only [Model.due, ha n hn.2, hx n hn.1 hn.2, hδ, hce, hcd]
  · simp only [Finset.mem_Icc] at hn
    rw [← ha n hn.2]; exact hy.1 n (by simp only [Finset.mem_Icc]; omega)
  · simp only [Finset.mem_Ico] at hn
    rw [← hx n hn.1 (by omega)]; exact hy.2 n (by simp only [Finset.mem_Ico]; omega)

lemma gamma_eq_of_agree {Ω' : Type*} [MeasurableSpace Ω'] (Q : Model Ω) (Q' : Model Ω')
    (ω : Ω) (ω' : Ω') (N : ℕ) (hδ : Q.δ = Q'.δ) (hce : Q.ce = Q'.ce) (hcd : Q.cd = Q'.cd)
    (hT : ∀ k, 1 ≤ k → k ≤ N → Q.T k ω = Q'.T k ω')
    (hx : ∀ k, 1 ≤ k → k ≤ N → Q.x k ω = Q'.x k ω') :
    Q.gamma 1 N ω = Q'.gamma 1 N ω' :=
  le_antisymm
    (gamma_le_of_agree Q' Q ω' ω N hδ.symm hce.symm hcd.symm
      (fun k h1 h2 => (hT k h1 h2).symm) (fun k h1 h2 => (hx k h1 h2).symm))
    (gamma_le_of_agree Q Q' ω ω' N hδ hce hcd hT hx)

/-- projection of an arbitrary `z` onto the feasible set of (12) for customers `1, …, N`. -/
noncomputable def proj (Q : Model Ω) (ω : Ω) (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => z 0
  | (n + 1) => if n = 0 then max (Q.arrival 1 ω) (z 1)
      else max (max (Q.arrival (n + 1) ω) (proj Q ω z n + Q.x n ω)) (z (n + 1))

lemma proj_feasible (Q : Model Ω) (ω : Ω) (z : ℕ → ℝ) (N : ℕ) :
    Q.IsSchedule 1 N (proj Q ω z) ω := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · simp only [Finset.mem_Icc] at hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [proj]
    split_ifs with h
    · subst h; exact le_max_left _ _
    · exact (le_max_left _ _).trans (le_max_left _ _)
  · simp only [Finset.mem_Ico] at hn
    have h : n ≠ 0 := by omega
    simp only [proj, h, if_false]
    exact (le_max_right _ _).trans (le_max_left _ _)

lemma proj_eq (Q : Model Ω) (ω : Ω) (z : ℕ → ℝ) (N : ℕ) (hz : Q.IsSchedule 1 N z ω) :
    ∀ n, 1 ≤ n → n ≤ N → proj Q ω z n = z n := by
  intro n h1 h2
  induction n with
  | zero => omega
  | succ m ih =>
    simp only [proj]
    split_ifs with h
    · subst h
      exact max_eq_right (hz.1 1 (by simp only [Finset.mem_Icc]; omega))
    · rw [ih (by omega) (by omega)]
      refine max_eq_right (max_le (hz.1 (m + 1) (by simp only [Finset.mem_Icc]; omega))
        (hz.2 m (by simp only [Finset.mem_Ico]; omega)))

lemma gamma_eq_iInf (Q : Model Ω) (ω : Ω) (N : ℕ) :
    Q.gamma 1 N ω = ⨅ z : ℕ → ℝ, ∑ n ∈ Finset.Icc 1 N,
      ENNReal.ofReal (g Q.ce Q.cd (proj Q ω z n + Q.x n ω - Q.due n ω)) := by
  apply le_antisymm
  · exact le_iInf fun z => iInf₂_le (proj Q ω z) (proj_feasible Q ω z N)
  · refine le_iInf₂ fun y hy => (iInf_le _ y).trans_eq ?_
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [Finset.mem_Icc] at hn
    rw [proj_eq Q ω y N hy n hn.1 hn.2]

/-- coordinates of the finite data vector -/
noncomputable def extT (N : ℕ) (v : Fin N ⊕ Fin N → ℝ) (k : ℕ) : ℝ :=
  if h : k - 1 < N then v (Sum.inl ⟨k - 1, h⟩) else 0

noncomputable def extX (N : ℕ) (v : Fin N ⊕ Fin N → ℝ) (k : ℕ) : ℝ :=
  if h : k - 1 < N then v (Sum.inr ⟨k - 1, h⟩) else 0

lemma continuous_extT (N k : ℕ) : Continuous fun v : Fin N ⊕ Fin N → ℝ => extT N v k := by
  unfold extT
  by_cases h : k - 1 < N
  · simp only [h, dif_pos]; exact continuous_apply _
  · simp only [h, dif_neg, not_false_eq_true]; exact continuous_const

lemma continuous_extX (N k : ℕ) : Continuous fun v : Fin N ⊕ Fin N → ℝ => extX N v k := by
  unfold extX
  by_cases h : k - 1 < N
  · simp only [h, dif_pos]; exact continuous_apply _
  · simp only [h, dif_neg, not_false_eq_true]; exact continuous_const

/-- the model on a one-point space built from a finite data vector -/
noncomputable def vecModel (N : ℕ) (δ ce cd : ℝ) (v : Fin N ⊕ Fin N → ℝ) : Model Unit :=
  ⟨fun k _ => extT N v k, fun k _ => extX N v k, δ, ce, cd⟩

noncomputable def F (N : ℕ) (δ ce cd : ℝ) (v : Fin N ⊕ Fin N → ℝ) : ℝ≥0∞ :=
  (vecModel N δ ce cd v).gamma 1 N ()

lemma continuous_arrival_vec (N : ℕ) (δ ce cd : ℝ) (n : ℕ) :
    Continuous fun v => (vecModel N δ ce cd v).arrival n () := by
  unfold Model.arrival
  exact continuous_finsetSum _ fun k _ => continuous_extT N k

lemma continuous_proj_vec (N : ℕ) (δ ce cd : ℝ) (z : ℕ → ℝ) (n : ℕ) :
    Continuous fun v => proj (vecModel N δ ce cd v) () z n := by
  induction n with
  | zero => exact continuous_const
  | succ m ih =>
    simp only [proj]
    by_cases h : m = 0
    · simp only [h, if_true]
      exact (continuous_arrival_vec N δ ce cd 1).max continuous_const
    · simp only [h, if_false]
      refine ((continuous_arrival_vec N δ ce cd (m + 1)).max (ih.add ?_)).max continuous_const
      exact continuous_extX N m

lemma measurable_F (N : ℕ) (δ ce cd : ℝ) : Measurable (F N δ ce cd) := by
  have : F N δ ce cd = fun v => ⨅ z : ℕ → ℝ, ∑ n ∈ Finset.Icc 1 N,
      ENNReal.ofReal (g ce cd (proj (vecModel N δ ce cd v) () z n + extX N v n
        - (vecModel N δ ce cd v).due n ())) := by
    funext v
    exact gamma_eq_iInf _ _ _
  rw [this]
  refine UpperSemicontinuous.measurable (upperSemicontinuous_iInf fun z => ?_)
  refine Continuous.upperSemicontinuous ?_
  refine continuous_finsetSum _ fun n _ => ENNReal.continuous_ofReal.comp ?_
  have hc : Continuous fun v => proj (vecModel N δ ce cd v) () z n + extX N v n
      - (vecModel N δ ce cd v).due n () := by
    unfold Model.due
    exact ((continuous_proj_vec N δ ce cd z n).add (continuous_extX N n)).sub
      ((continuous_arrival_vec N δ ce cd n).add continuous_const)
  unfold g
  exact (continuous_const.mul (hc.neg.max continuous_const)).add
    (continuous_const.mul (hc.max continuous_const))

/-- the data vector of block `s`: inter-arrival and service times of customers `s+1, …, s+N`. -/
def X (Q : Model Ω) (N s : ℕ) (ω : Ω) : Fin N ⊕ Fin N → ℝ :=
  fun j => Sum.elim (fun n => Q.T (n + 1)) (fun n => Q.x (n + 1))
    (Sum.map (fun i : Fin N => s + (i : ℕ)) (fun i : Fin N => s + (i : ℕ)) j) ω

lemma gamma_block_eq (Q : Model Ω) (N s : ℕ) (ω : Ω) :
    Q.gamma (s + 1) (s + N) ω = F N Q.δ Q.ce Q.cd (X Q N s ω) := by
  rw [gamma_shift]
  unfold F
  refine gamma_eq_of_agree _ _ ω () N rfl rfl rfl (fun k h1 h2 => ?_) (fun k h1 h2 => ?_)
  · have h : k - 1 < N := by omega
    simp only [shift, vecModel, extT, h, dif_pos, X, Sum.map_inl, Sum.elim_inl]
    congr 1; omega
  · have h : k - 1 < N := by omega
    simp only [shift, vecModel, extX, h, dif_pos, X, Sum.map_inr, Sum.elim_inr]
    congr 1; omega

end SQCBlockAux

open SQCBlockAux ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Q : Model Ω)
    (hQ : Q.Standing μ) (N : ℕ) :
    ∫⁻ ω, Q.gamma 1 N ω ∂μ = ∫⁻ ω, Q.gamma (N + 1) (2 * N) ω ∂μ := by
  obtain ⟨hP, hTm, hxm, hind, hTid, hxid, -⟩ := hQ
  set f : ℕ ⊕ ℕ → Ω → ℝ := fun i => Sum.elim (fun n => Q.T (n + 1)) (fun n => Q.x (n + 1)) i
    with hf
  have hfm : ∀ i, Measurable (f i) := by
    rintro (n | n)
    · exact hTm (n + 1) (by omega)
    · exact hxm (n + 1) (by omega)
  let e : ℕ → Fin N ⊕ Fin N → ℕ ⊕ ℕ := fun s =>
    Sum.map (fun i : Fin N => s + (i : ℕ)) (fun i : Fin N => s + (i : ℕ))
  have he : ∀ s, Function.Injective (e s) := by
    intro s
    refine Sum.map_injective.2 ⟨fun i j h => ?_, fun i j h => ?_⟩ <;>
      exact Fin.ext (by simpa using h)
  have hXm : ∀ s, Measurable (X Q N s) := fun s =>
    measurable_pi_lambda _ fun j => hfm (e s j)
  have hlaw : ∀ s, μ.map (X Q N s) = Measure.pi (fun j => μ.map (f (e s j))) := by
    intro s
    have hi := hind.precomp (he s)
    exact (iIndepFun_iff_map_fun_eq_pi_map (fun j => (hfm (e s j)).aemeasurable)).1 hi
  have hmarg : ∀ s, (fun j => μ.map (f (e s j))) = (fun j => μ.map (f (e 0 j))) := by
    intro s
    funext j
    rcases j with i | i
    · change μ.map (Q.T (s + i + 1)) = μ.map (Q.T (0 + i + 1))
      rw [(hTid (s + i + 1) (by omega)).map_eq, (hTid (0 + i + 1) (by omega)).map_eq]
    · change μ.map (Q.x (s + i + 1)) = μ.map (Q.x (0 + i + 1))
      rw [(hxid (s + i + 1) (by omega)).map_eq, (hxid (0 + i + 1) (by omega)).map_eq]
  have hint : ∀ s, ∫⁻ ω, Q.gamma (s + 1) (s + N) ω ∂μ =
      ∫⁻ v, F N Q.δ Q.ce Q.cd v ∂(Measure.pi (fun j => μ.map (f (e 0 j)))) := by
    intro s
    simp_rw [gamma_block_eq]
    rw [← lintegral_map (measurable_F N Q.δ Q.ce Q.cd) (hXm s), hlaw s, hmarg s]
  have h0 := hint 0
  have hN := hint N
  simp only [zero_add] at h0
  rw [two_mul, h0, hN]
