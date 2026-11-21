-- Prove2me | solution 1 for OptimalAgnosticPAC.Learner.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T11:31:15.729115+00:00
-- url     : https://prove2.me/submissions/09b13d18-d531-4dcb-a339-6f4fcfbe2b04

import Mathlib
import Definitions.Def_OptimalAgnosticPAC_Learner_Score
import Definitions.Def_HighDimProb_Chaining_VcDim

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.T3
open OptimalAgnosticPAC.Learner

theorem loss_eq (a : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1) (y : Bool) :
    loss a y = (1 - sgn y * a) / 2 := by
  obtain ⟨h1, h2⟩ := ha
  unfold loss sgn
  cases y
  · simp only [Bool.false_eq_true, if_false]
    rw [abs_of_nonneg (by linarith)]; ring
  · simp only [if_true]
    rw [abs_of_nonpos (by linarith)]; ring

end OptimalAgnosticPAC.Dev.T3
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L32
open OptimalAgnosticPAC.Learner

theorem sum_succ {Z : Type} (w : (t : ℕ) → (Fin t → Z) → Z → ℝ) (m : ℕ) (S : Fin (m + 1) → Z) :
    ∑ t : Fin (m + 1), w t (prefixSample S t t.isLt.le) (S t) =
      ∑ t : Fin m, w t (prefixSample (fun i : Fin m => S (Fin.castSucc i)) t t.isLt.le)
        (S (Fin.castSucc t)) + w m (fun i : Fin m => S (Fin.castSucc i)) (S (Fin.last m)) := by
  rw [Fin.sum_univ_castSucc]
  congr 1

theorem measurable_sum {Z : Type} [MeasurableSpace Z] (w : (t : ℕ) → (Fin t → Z) → Z → ℝ)
    (hw : ∀ t, Measurable (fun p : (Fin t → Z) × Z => w t p.1 p.2)) (m : ℕ) :
    Measurable (fun S : Fin m → Z => ∑ t : Fin m, w t (prefixSample S t t.isLt.le) (S t)) := by
  refine Finset.measurable_sum _ (fun t _ => ?_)
  have h1 : Measurable (fun S : Fin m → Z => (prefixSample S t t.isLt.le, S t)) := by
    refine Measurable.prodMk ?_ (measurable_pi_apply _)
    exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)
  exact (hw t).comp h1

/-- Iterated conditional exponential bound. -/
theorem exp_sum_le {Z : Type} [MeasurableSpace Z] (P : Measure Z) [IsProbabilityMeasure P]
    (w : (t : ℕ) → (Fin t → Z) → Z → ℝ)
    (hw : ∀ t, Measurable (fun p : (Fin t → Z) × Z => w t p.1 p.2))
    (h1 : ∀ t s, ∫⁻ z, ENNReal.ofReal (Real.exp (w t s z)) ∂P ≤ 1) (m : ℕ) :
    ∫⁻ S, ENNReal.ofReal (Real.exp (∑ t : Fin m, w t (prefixSample S t t.isLt.le) (S t)))
      ∂(Measure.pi (fun _ : Fin m => P)) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    set μ : Measure (Fin (m + 1) → Z) := Measure.pi (fun _ : Fin (m + 1) => P) with hμ
    set μm : Measure (Fin m → Z) := Measure.pi (fun _ : Fin m => P) with hμm
    set F : (Fin (m + 1) → Z) → ENNReal := fun S =>
      ENNReal.ofReal (Real.exp (∑ t : Fin (m + 1), w t (prefixSample S t t.isLt.le) (S t))) with hF
    have hFm : Measurable F :=
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_sum w hw (m + 1))))
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => P) (Fin.last m)
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Z) (Fin.last m) with he
    have step1 : ∫⁻ S, F S ∂μ = ∫⁻ p, F (e.symm p) ∂(P.prod μm) := by
      have := hmp.lintegral_comp_emb e.measurableEmbedding (fun p => F (e.symm p))
      simp only [MeasurableEquiv.symm_apply_apply] at this
      rw [this]
    have hFe : Measurable (fun p => F (e.symm p)) := hFm.comp e.symm.measurable
    have hsy : ∀ (z : Z) (s : Fin m → Z), (∀ i : Fin m, (e.symm (z, s)) (Fin.castSucc i) = s i) ∧
        (e.symm (z, s)) (Fin.last m) = z := by
      intro z s
      refine ⟨?_, ?_⟩
      · intro i
        have : Fin.castSucc i = (Fin.last m).succAbove i := by
          rw [Fin.succAbove_last]
        rw [this]
        simp [he, MeasurableEquiv.piFinSuccAbove]
      · simp [he, MeasurableEquiv.piFinSuccAbove]
    have hFs : ∀ (z : Z) (s : Fin m → Z), F (e.symm (z, s)) =
        ENNReal.ofReal (Real.exp (∑ t : Fin m, w t (prefixSample s t t.isLt.le) (s t))) *
          ENNReal.ofReal (Real.exp (w m s z)) := by
      intro z s
      obtain ⟨h1', h2'⟩ := hsy z s
      simp only [hF]
      rw [sum_succ]
      simp only [h1', h2', Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    rw [step1, lintegral_prod_symm _ hFe.aemeasurable]
    calc ∫⁻ s, ∫⁻ z, F (e.symm (z, s)) ∂P ∂μm
        ≤ ∫⁻ s, ENNReal.ofReal (Real.exp (∑ t : Fin m, w t (prefixSample s t t.isLt.le) (s t))) ∂μm := by
          refine lintegral_mono (fun s => ?_)
          simp only [hFs]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          calc _ ≤ ENNReal.ofReal (Real.exp (∑ t : Fin m, w t (prefixSample s t t.isLt.le) (s t))) * 1 :=
                by gcongr; exact h1 m s
            _ = _ := mul_one _
      _ ≤ 1 := ih
end OptimalAgnosticPAC.Dev.L32
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L32

theorem exp_le_quad (x : ℝ) (hx : |x| ≤ 1) : Real.exp x ≤ 1 + x + (3 / 4) * x ^ 2 := by
  have h := Real.exp_bound (x := x) hx (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [Nat.factorial] at h
  have h3 : |x| ^ 3 ≤ x ^ 2 := by
    have : |x| ^ 3 = |x| * x ^ 2 := by rw [pow_succ, sq_abs]; ring
    rw [this]
    nlinarith [sq_nonneg x, abs_nonneg x]
  have := (abs_le.mp h).2
  nlinarith [sq_nonneg x]

end OptimalAgnosticPAC.Dev.L32
end

section
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L32

theorem card_suffix (k : ℕ) :
    (Finset.univ.filter (fun t : Fin (2 * k) => k ≤ t.val)).card = k := by
  rw [← Finset.card_map Fin.valEmbedding]
  have : (Finset.univ.filter (fun t : Fin (2 * k) => k ≤ t.val)).map Fin.valEmbedding =
      Finset.Ico k (2 * k) := by
    ext n
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨ht, t.isLt⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨n, h2⟩, h1, rfl⟩
  rw [this]; simp; omega

end OptimalAgnosticPAC.Dev.L32
end

section
open MeasureTheory
open scoped Classical

namespace OptimalAgnosticPAC.Dev.L32
open OptimalAgnosticPAC.Learner

theorem loss_mem (a : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1) (y : Bool) : 0 ≤ loss a y ∧ loss a y ≤ 1 := by
  rw [T3.loss_eq a ha y]
  obtain ⟨h1, h2⟩ := ha
  unfold sgn
  split_ifs <;> constructor <;> linarith

theorem meas_joint {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ)
    (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (hq : IsLOOScore H d q) (t : ℕ) :
    Measurable (fun p : (Fin t → X × Bool) × (X × Bool) => loss (q t p.1 p.2.1) p.2.2) := by
  unfold loss
  have h1 : Measurable (fun p : (Fin t → X × Bool) × (X × Bool) => sgn p.2.2) :=
    (measurable_from_top (f := sgn)).comp (measurable_snd.comp measurable_snd)
  have h2 : Measurable (fun p : (Fin t → X × Bool) × (X × Bool) => q t p.1 p.2.1) :=
    (hq.measurable t).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact ((h2.sub h1).abs).div_const 2

theorem meas_ind {X : Type} [MeasurableSpace X] (h : X → Bool) (hh : Measurable h) :
    MeasurableSet {z : X × Bool | h z.1 ≠ z.2} := by
  have : MeasurableSet {z : X × Bool | h z.1 = z.2} :=
    measurableSet_eq_fun (hh.comp measurable_fst) measurable_snd
  exact this.compl

end OptimalAgnosticPAC.Dev.L32

namespace OptimalAgnosticPAC.Learner
open OptimalAgnosticPAC.Dev.L32

end OptimalAgnosticPAC.Learner
end

section
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L31
open OptimalAgnosticPAC.Learner

noncomputable def Phi (m : ℕ) (i : Fin (m + 1)) (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + 1)) :=
  (finSuccEquiv' (Fin.last m)).trans ((Equiv.optionCongr σ).trans (finSuccEquiv' i).symm)

theorem Phi_castSucc (m : ℕ) (i : Fin (m + 1)) (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    Phi m i σ (Fin.castSucc j) = i.succAbove (σ j) := by
  have h1 : Fin.castSucc j = (Fin.last m).succAbove j := by rw [Fin.succAbove_last]
  rw [h1]
  simp only [Phi, Equiv.trans_apply, finSuccEquiv'_succAbove, Equiv.optionCongr_apply, Option.map_some, finSuccEquiv'_symm_some]

theorem Phi_last (m : ℕ) (i : Fin (m + 1)) (σ : Equiv.Perm (Fin m)) :
    Phi m i σ (Fin.last m) = i := by
  simp [Phi, finSuccEquiv'_at, Equiv.symm_apply_eq]

theorem Phi_bij (m : ℕ) : Function.Bijective (fun p : Fin (m + 1) × Equiv.Perm (Fin m) => Phi m p.1 p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, ?_⟩
  · rintro ⟨i, σ⟩ ⟨i', σ'⟩ h
    simp only at h
    have h1 : i = i' := by
      have := congrArg (fun e : Equiv.Perm (Fin (m + 1)) => e (Fin.last m)) h
      simpa [Phi_last] using this
    subst h1
    have : σ = σ' := by
      ext j
      have := congrArg (fun e : Equiv.Perm (Fin (m + 1)) => e (Fin.castSucc j)) h
      simp only [Phi_castSucc] at this
      exact congrArg Fin.val (i.succAbove_right_injective this)
    rw [this]
  · simp [Fintype.card_perm, Nat.factorial_succ]

theorem sum_perm_succ (m : ℕ) (F : Equiv.Perm (Fin (m + 1)) → ℝ) :
    ∑ π, F π = ∑ i : Fin (m + 1), ∑ σ : Equiv.Perm (Fin m), F (Phi m i σ) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_bijective _ (Phi_bij m) _ _ (fun _ => rfl)).symm


def pre {Z : Type} {M : ℕ} (V : Fin M → Z) (t : Fin M) : Fin (t.val + 1) → Z :=
  fun j => V ⟨j.val, by have := j.isLt; have := t.isLt; omega⟩

theorem comp_Phi {Z : Type} (m : ℕ) (S : Fin (m + 1) → Z) (i : Fin (m + 1))
    (σ : Equiv.Perm (Fin m)) :
    (S ∘ (Phi m i σ)) = (Fin.snoc (α := fun _ => Z) (deleteObs S i ∘ σ) (S i)) := by
  funext x
  refine Fin.lastCases ?_ (fun j => ?_) x
  · simp [Phi_last]
  · simp [Phi_castSucc, deleteObs]

theorem sum_pre_snoc {Z : Type} (M : ℕ) (U : Fin M → Z) (z : Z) (ψ : (t : ℕ) → (Fin (t + 1) → Z) → ℝ) :
    ∑ t : Fin (M + 1), ψ t (pre (Fin.snoc (α := fun _ => Z) U z) t) =
      ∑ t : Fin M, ψ t (pre U t) + ψ M (Fin.snoc (α := fun _ => Z) U z) := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl (fun t _ => ?_)
    congr 1
    funext j
    have hj : (j : ℕ) < M := by have := j.isLt; have := t.isLt; simp only [Fin.coe_castSucc] at *; omega
    simp [pre, Fin.snoc, hj]

theorem perm_exp {Z : Type} (ψ : (t : ℕ) → (Fin (t + 1) → Z) → ℝ)
    (G : (n : ℕ) → (Fin n → Z) → Prop)
    (hG : ∀ n (T : Fin (n + 1) → Z) (i : Fin (n + 1)), G (n + 1) T → G n (deleteObs T i))
    (hsym : ∀ t (U : Fin t → Z) (σ : Equiv.Perm (Fin t)) (z : Z),
      ψ t (Fin.snoc (α := fun _ => Z) (U ∘ σ) z) = ψ t (Fin.snoc (α := fun _ => Z) U z))
    (hC : ∀ t (T : Fin (t + 1) → Z), G (t + 1) T →
      ∑ i : Fin (t + 1), Real.exp (ψ t (Fin.snoc (α := fun _ => Z) (deleteObs T i) (T i))) ≤ (t : ℝ) + 1) :
    ∀ (M : ℕ) (S : Fin M → Z), G M S →
      ∑ π : Equiv.Perm (Fin M), Real.exp (∑ t : Fin M, ψ t (pre (S ∘ π) t)) ≤ (M.factorial : ℝ) := by
  intro M
  induction M with
  | zero => intro S _; simp
  | succ M ih =>
    intro S hS
    rw [sum_perm_succ]
    have e : ∀ (i : Fin (M + 1)) (σ : Equiv.Perm (Fin M)),
        Real.exp (∑ t : Fin (M + 1), ψ t (pre (S ∘ (Phi M i σ)) t)) =
        Real.exp (ψ M (Fin.snoc (α := fun _ => Z) (deleteObs S i) (S i))) *
          Real.exp (∑ t : Fin M, ψ t (pre (deleteObs S i ∘ σ) t)) := by
      intro i σ
      rw [comp_Phi, sum_pre_snoc, Real.exp_add, mul_comm, hsym]
    simp only [e]
    have : ∀ i : Fin (M + 1), ∑ σ : Equiv.Perm (Fin M),
        Real.exp (ψ M (Fin.snoc (α := fun _ => Z) (deleteObs S i) (S i))) *
          Real.exp (∑ t : Fin M, ψ t (pre (deleteObs S i ∘ σ) t)) ≤
        Real.exp (ψ M (Fin.snoc (α := fun _ => Z) (deleteObs S i) (S i))) * (M.factorial : ℝ) := by
      intro i
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (ih _ (hG M S i hS)) (Real.exp_pos _).le
    calc _ ≤ ∑ i : Fin (M + 1), Real.exp (ψ M (Fin.snoc (α := fun _ => Z) (deleteObs S i) (S i))) * (M.factorial : ℝ) :=
          Finset.sum_le_sum (fun i _ => this i)
      _ = (∑ i : Fin (M + 1), Real.exp (ψ M (Fin.snoc (α := fun _ => Z) (deleteObs S i) (S i)))) * (M.factorial : ℝ) := by
          rw [Finset.sum_mul]
      _ ≤ ((M : ℝ) + 1) * (M.factorial : ℝ) := mul_le_mul_of_nonneg_right (hC M S hS) (by positivity)
      _ = ((M + 1).factorial : ℝ) := by rw [Nat.factorial_succ]; push_cast; ring

end OptimalAgnosticPAC.Dev.L31
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L31
open OptimalAgnosticPAC.Learner

section
variable {X : Type} [MeasurableSpace X]

noncomputable def Dl (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (h : X → Bool) (t : ℕ)
    (U : Fin t → X × Bool) (z : X × Bool) : ℝ :=
  loss (q t U z.1) z.2 - (if h z.1 ≠ z.2 then 1 else 0)

noncomputable def wf (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (h : X → Bool) (k : ℕ) (lam c : ℝ)
    (t : ℕ) (U : Fin t → X × Bool) (z : X × Bool) : ℝ :=
  if k ≤ t then lam * Dl q h t U z - c else 0

noncomputable def psi (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (h : X → Bool) (k : ℕ) (lam c : ℝ)
    (t : ℕ) (W : Fin (t + 1) → X × Bool) : ℝ :=
  wf q h k lam c t (fun j => W j.castSucc) (W (Fin.last t))

theorem psi_snoc (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (h : X → Bool) (k : ℕ) (lam c : ℝ)
    (t : ℕ) (U : Fin t → X × Bool) (z : X × Bool) :
    psi q h k lam c t (Fin.snoc (α := fun _ => X × Bool) U z) = wf q h k lam c t U z := by
  simp [psi]

noncomputable def cnt {n : ℕ} (h : X → Bool) (T : Fin n → X × Bool) : ℕ :=
  (Finset.univ.filter (fun i => h (T i).1 ≠ (T i).2)).card

theorem cnt_del {n : ℕ} (h : X → Bool) (T : Fin (n + 1) → X × Bool) (i : Fin (n + 1)) :
    cnt h (deleteObs T i) ≤ cnt h T := by
  unfold cnt
  refine Finset.card_le_card_of_injOn i.succAbove ?_ (Fin.succAbove_right_injective.injOn)
  intro j hj
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hj ⊢
  simpa [deleteObs] using hj

noncomputable def muC (d : ℕ) (N0 : ℝ) (k : ℕ) : ℝ :=
  120 * Real.sqrt ((d : ℝ) * N0 / (k : ℝ) ^ 2) + 7202 * (d : ℝ) / (k : ℝ)

noncomputable def vC (d : ℕ) (N0 : ℝ) (k : ℕ) : ℝ := muC d N0 k + 2 * N0 / (k : ℝ)

theorem pt (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1) (l I c : ℝ) (hl : 0 ≤ l) (hl' : l ≤ 1)
    (hI : I = 0 ∨ I = 1) :
    Real.exp (lam * (l - I) - c) ≤
      Real.exp (-c) * (1 + lam * (l - I) + (3 / 4) * lam ^ 2 * ((l - I) + 2 * I)) := by
  have hI0 : 0 ≤ I := by rcases hI with h | h <;> rw [h] <;> norm_num
  have hI1 : I ≤ 1 := by rcases hI with h | h <;> rw [h] <;> norm_num
  have hx : |lam * (l - I)| ≤ 1 := by
    rw [abs_le]; constructor <;> nlinarith
  have h1 := L32.exp_le_quad _ hx
  have hd : (l - I) ^ 2 ≤ l + I := by
    nlinarith [mul_nonneg hl hI0, mul_nonneg hl (sub_nonneg.mpr hl'), mul_nonneg hI0 (sub_nonneg.mpr hI1)]
  have : Real.exp (lam * (l - I) - c) = Real.exp (-c) * Real.exp (lam * (l - I)) := by
    rw [mul_comm, ← Real.exp_add]; ring_nf
  rw [this]
  refine mul_le_mul_of_nonneg_left (h1.trans ?_) (Real.exp_pos _).le
  have : (lam * (l - I)) ^ 2 = lam ^ 2 * (l - I) ^ 2 := by ring
  rw [this]
  nlinarith [sq_nonneg lam]

theorem step_C {H : Set (X → Bool)} {d : ℕ} (hd : 1 ≤ d)
    {q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ} (hq : IsLOOScore H d q)
    {h : X → Bool} (hh : h ∈ H) {k : ℕ} (hk : 1 ≤ k) {lam N0 : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (t : ℕ) (T : Fin (t + 1) → X × Bool) (hT : (cnt h T : ℝ) ≤ N0) :
    ∑ i : Fin (t + 1), Real.exp (wf q h k lam (lam * muC d N0 k + (3 / 4) * lam ^ 2 * vC d N0 k) t
      (deleteObs T i) (T i)) ≤ (t : ℝ) + 1 := by
  set c := lam * muC d N0 k + (3 / 4) * lam ^ 2 * vC d N0 k with hc
  by_cases hkt : k ≤ t
  · have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hkt' : (k : ℝ) ≤ t + 1 := by have : (k : ℝ) ≤ t := by exact_mod_cast hkt
                                      linarith
    have hN0 : 0 ≤ N0 := le_trans (Nat.cast_nonneg _) hT
    set l : Fin (t + 1) → ℝ := fun i => loss (q t (deleteObs T i) (T i).1) (T i).2 with hl
    set I : Fin (t + 1) → ℝ := fun i => if h (T i).1 ≠ (T i).2 then 1 else 0 with hI
    have hl0 : ∀ i, 0 ≤ l i := fun i => (L32.loss_mem _ (hq.mem_Icc t _ _) _).1
    have hl1 : ∀ i, l i ≤ 1 := fun i => (L32.loss_mem _ (hq.mem_Icc t _ _) _).2
    have hI01 : ∀ i, I i = 0 ∨ I i = 1 := fun i => by
      simp only [hI]; split_ifs <;> simp
    have hpt : ∀ i, Real.exp (wf q h k lam c t (deleteObs T i) (T i)) ≤
        Real.exp (-c) * (1 + lam * (l i - I i) + (3 / 4) * lam ^ 2 * ((l i - I i) + 2 * I i)) := by
      intro i
      have : wf q h k lam c t (deleteObs T i) (T i) = lam * (l i - I i) - c := by
        simp [wf, hkt, Dl, hl, hI]
      rw [this]
      exact pt lam hlam0 hlam1 _ _ _ (hl0 i) (hl1 i) (hI01 i)
    have hsumI : ∑ i, I i = (cnt h T : ℝ) := by
      simp only [hI, cnt]
      rw [Finset.sum_boole]
    -- the leave-one-out bound
    have hloo := hq.loo_bound t T
    have hsuml : ∑ i, l i = (1 / 2) * ∑ i, |q t (deleteObs T i) (T i).1 - sgn (T i).2| := by
      simp only [hl, loss]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => by ring)
    have hemp : empMinRisk H T ≤ (cnt h T : ℝ) / ((t : ℝ) + 1) := by
      unfold empMinRisk
      have : (sInf ((fun h => errCount h T) '' H) : ℕ) ≤ cnt h T :=
        Nat.sInf_le ⟨h, hh, rfl⟩
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_succ]
      gcongr
    have hemp0 : 0 ≤ empMinRisk H T := by unfold empMinRisk; positivity
    have ht1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have hsq : Real.sqrt ((d : ℝ) * empMinRisk H T / ((t : ℝ) + 1)) ≤
        Real.sqrt ((d : ℝ) * N0 / (k : ℝ) ^ 2) := by
      apply Real.sqrt_le_sqrt
      have h1 : empMinRisk H T ≤ N0 / ((t : ℝ) + 1) := hemp.trans (by gcongr)
      calc (d : ℝ) * empMinRisk H T / ((t : ℝ) + 1) ≤ (d : ℝ) * (N0 / ((t : ℝ) + 1)) / ((t : ℝ) + 1) := by
            gcongr
        _ = (d : ℝ) * N0 / (((t : ℝ) + 1) * ((t : ℝ) + 1)) := by field_simp
        _ ≤ (d : ℝ) * N0 / (k : ℝ) ^ 2 := by
            rw [sq]; gcongr
    have hd7 : 7202 * ((d : ℝ) / ((t : ℝ) + 1)) ≤ 7202 * (d : ℝ) / (k : ℝ) := by
      rw [mul_div_assoc']
      gcongr
    have hsumD : ∑ i, (l i - I i) ≤ ((t : ℝ) + 1) * muC d N0 k := by
      rw [Finset.sum_sub_distrib, hsumI]
      have h1 : ∑ i, l i ≤ ((t : ℝ) + 1) * (empMinRisk H T + 120 * Real.sqrt ((d : ℝ) * empMinRisk H T / ((t : ℝ) + 1)) +
          7202 * ((d : ℝ) / ((t : ℝ) + 1))) := by
        rw [hsuml]
        have : (1 / (2 * ((t : ℝ) + 1))) * ∑ i, |q t (deleteObs T i) (T i).1 - sgn (T i).2| =
            (1 / ((t : ℝ) + 1)) * ((1 / 2) * ∑ i, |q t (deleteObs T i) (T i).1 - sgn (T i).2|) := by
          field_simp
        rw [this] at hloo
        have := mul_le_mul_of_nonneg_left hloo ht1.le
        rw [← mul_assoc, mul_one_div_cancel ht1.ne', one_mul] at this
        exact this
      have h2 : ((t : ℝ) + 1) * empMinRisk H T ≤ (cnt h T : ℝ) := by
        calc _ ≤ ((t : ℝ) + 1) * ((cnt h T : ℝ) / ((t : ℝ) + 1)) := by gcongr
          _ = _ := by field_simp
      have h3 : ((t : ℝ) + 1) * (120 * Real.sqrt ((d : ℝ) * empMinRisk H T / ((t : ℝ) + 1)) +
          7202 * ((d : ℝ) / ((t : ℝ) + 1))) ≤ ((t : ℝ) + 1) * muC d N0 k := by
        unfold muC; gcongr
      nlinarith
    have hsumI' : ∑ i, I i ≤ ((t : ℝ) + 1) * (N0 / k) := by
      rw [hsumI]
      calc (cnt h T : ℝ) ≤ N0 := hT
        _ = k * (N0 / k) := by field_simp
        _ ≤ ((t : ℝ) + 1) * (N0 / k) := by gcongr
    calc ∑ i, Real.exp (wf q h k lam c t (deleteObs T i) (T i))
        ≤ ∑ i, Real.exp (-c) * (1 + lam * (l i - I i) + (3 / 4) * lam ^ 2 * ((l i - I i) + 2 * I i)) :=
          Finset.sum_le_sum (fun i _ => hpt i)
      _ = Real.exp (-c) * (((t : ℝ) + 1) + (lam + (3 / 4) * lam ^ 2) * ∑ i, (l i - I i) +
            (3 / 2) * lam ^ 2 * ∑ i, I i) := by
          rw [← Finset.mul_sum]
          congr 1
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_one, ← Finset.mul_sum]
          push_cast
          ring
      _ ≤ Real.exp (-c) * (((t : ℝ) + 1) * (1 + c)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          have a1 : (lam + (3 / 4) * lam ^ 2) * ∑ i, (l i - I i) ≤
              (lam + (3 / 4) * lam ^ 2) * (((t : ℝ) + 1) * muC d N0 k) :=
            mul_le_mul_of_nonneg_left hsumD (by positivity)
          have a2 : (3 / 2) * lam ^ 2 * ∑ i, I i ≤ (3 / 2) * lam ^ 2 * (((t : ℝ) + 1) * (N0 / k)) :=
            mul_le_mul_of_nonneg_left hsumI' (by positivity)
          have e : ((t : ℝ) + 1) * (1 + c) = ((t : ℝ) + 1) + (lam + (3 / 4) * lam ^ 2) *
              (((t : ℝ) + 1) * muC d N0 k) + (3 / 2) * lam ^ 2 * (((t : ℝ) + 1) * (N0 / k)) := by
            simp only [hc, vC]; field_simp; ring
          linarith
      _ ≤ ((t : ℝ) + 1) := by
          have h1 : (1 + c) * Real.exp (-c) ≤ 1 := by
            have := Real.add_one_le_exp c
            have h4 : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
            nlinarith [Real.exp_pos (-c)]
          nlinarith [ht1]
  · simp [wf, hkt]

end
end OptimalAgnosticPAC.Dev.L31
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L31
open OptimalAgnosticPAC.Learner

theorem lam_pick (v ℓ k : ℝ) (hv : 0 < v) (hℓ : 0 < ℓ) (hk : 0 < k) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
      (3 / 4) * lam * v + ℓ / (lam * k) ≤ 2 * Real.sqrt (ℓ * v / k) + ℓ / k := by
  set r := Real.sqrt (ℓ * v / k) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by positivity)
  have hr2 : r ^ 2 = ℓ * v / k := Real.sq_sqrt (by positivity)
  have hb : 0 ≤ ℓ / k := by positivity
  by_cases hc : r ≤ v
  · refine ⟨r / v, by positivity, by rw [div_le_one hv]; exact hc, ?_⟩
    have e1 : (3 / 4) * (r / v) * v = (3 / 4) * r := by field_simp
    have e2 : ℓ / (r / v * k) = r := by
      have : ℓ = r ^ 2 * k / v := by rw [hr2]; field_simp
      rw [this]; field_simp
    rw [e1, e2]; linarith
  · push Not at hc
    refine ⟨1, by norm_num, le_rfl, ?_⟩
    simp only [mul_one, one_mul]
    linarith

theorem num_main (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (L ℓ : ℝ) (hL : 0 ≤ L) (hℓ : 0 < ℓ) :
    ∃ lam : ℝ, 0 < lam ∧ lam ≤ 1 ∧
      muC d (4 * k * L + 2 * ℓ) k + (3 / 4) * lam * vC d (4 * k * L + 2 * ℓ) k +
        ℓ / (lam * k) ≤
      8200 * (Real.sqrt (L * ((d : ℝ) + ℓ) / (k : ℝ)) + ((d : ℝ) + ℓ) / (k : ℝ)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set N0 := 4 * (k : ℝ) * L + 2 * ℓ with hN0
  set a := (d : ℝ) / k with ha
  set b := ℓ / (k : ℝ) with hb
  set T := Real.sqrt (L * ((d : ℝ) + ℓ) / (k : ℝ)) with hT
  have ha0 : 0 < a := by positivity
  have hb0 : 0 < b := by positivity
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  have hT2 : T ^ 2 = L * (a + b) := by
    rw [hT, Real.sq_sqrt (by positivity)]; rw [ha, hb]; field_simp
  have hsqrt : Real.sqrt ((d : ℝ) * N0 / (k : ℝ) ^ 2) ≤ 2 * T + (a + b) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have e : (d : ℝ) * N0 / (k : ℝ) ^ 2 = 4 * L * a + 2 * a * b := by
      rw [hN0, ha, hb]; field_simp
    rw [e]
    nlinarith [mul_nonneg hT0 (add_pos ha0 hb0).le, mul_nonneg hL hb0.le, sq_nonneg (a - b)]
  have hmu : muC d N0 k ≤ 240 * T + 7322 * (a + b) := by
    unfold muC
    have : 7202 * (d : ℝ) / k = 7202 * a := by rw [ha]; ring
    rw [this]; nlinarith
  have hmu0 : 7202 * a ≤ muC d N0 k := by
    unfold muC
    have : 7202 * (d : ℝ) / k = 7202 * a := by rw [ha]; ring
    rw [this]; have := Real.sqrt_nonneg ((d : ℝ) * N0 / (k : ℝ) ^ 2); linarith
  set v := vC d N0 k with hv
  have hvdef : v = muC d N0 k + 8 * L + 4 * b := by
    rw [hv, vC, hN0, hb]; field_simp; ring
  have hv0 : 0 < v := by rw [hvdef]; nlinarith
  have hvle : v ≤ 240 * T + 7326 * (a + b) + 8 * L := by rw [hvdef]; nlinarith
  obtain ⟨lam, hl0, hl1, hlam⟩ := lam_pick v ℓ k hv0 hℓ hkR
  refine ⟨lam, hl0, hl1, ?_⟩
  set r := Real.sqrt (ℓ * v / k) with hr
  have hr2 : r ^ 2 = ℓ * v / k := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrle : r ≤ 87 * (a + b) + 12 * T := by
    by_contra hcon
    push Not at hcon
    have h1 : (87 * (a + b) + 12 * T) ^ 2 < r ^ 2 := by
      apply pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
    have h2 : r ^ 2 = b * v := by rw [hr2, hb]; ring
    have h3 : b * v ≤ (a + b) * v := by nlinarith
    have h4 : (a + b) * v ≤ (a + b) * (240 * T + 7326 * (a + b) + 8 * L) :=
      mul_le_mul_of_nonneg_left hvle (by positivity)
    nlinarith [mul_nonneg hT0 (add_pos ha0 hb0).le]
  have hbu : b ≤ a + b := by linarith
  have : (3 / 4) * lam * v + ℓ / (lam * k) ≤ 2 * r + b := by rw [hb]; exact hlam
  have hfin : muC d N0 k + (3 / 4) * lam * v + ℓ / (lam * k) ≤ 8200 * (T + (a + b)) := by
    nlinarith
  have e : ((d : ℝ) + ℓ) / (k : ℝ) = a + b := by rw [ha, hb]; ring
  rw [e]; exact hfin

end OptimalAgnosticPAC.Dev.L31
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L31

theorem pi_comp_perm {α : Type} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P] (n : ℕ)
    (π : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun S : Fin n → α => S ∘ π) (Measure.pi (fun _ : Fin n => P))
      (Measure.pi (fun _ : Fin n => P)) := by
  have := measurePreserving_piCongrLeft (fun _ : Fin n => P) π.symm
  convert this using 1
  funext S
  ext i
  simp [MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

theorem perm_avg {α : Type} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P] (n : ℕ)
    (B : Set (Fin n → α)) (hB : MeasurableSet B) (a : ℝ)
    (hcount : ∀ S : Fin n → α,
      ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => S ∘ π ∈ B)).card : ℝ) ≤ a * (n.factorial : ℝ)) :
    Measure.pi (fun _ : Fin n => P) B ≤ ENNReal.ofReal a := by
  set μ := Measure.pi (fun _ : Fin n => P) with hμ
  have h1 : ∀ π : Equiv.Perm (Fin n), μ ((fun S : Fin n → α => S ∘ π) ⁻¹' B) = μ B := fun π =>
    (pi_comp_perm P n π).measure_preimage hB.nullMeasurableSet
  have h2 : ∀ π : Equiv.Perm (Fin n), ∫⁻ S, B.indicator 1 (S ∘ π) ∂μ = μ B := by
    intro π
    have hm : MeasurableSet ((fun S : Fin n → α => S ∘ π) ⁻¹' B) :=
      (pi_comp_perm P n π).measurable hB
    have : (fun S : Fin n → α => B.indicator (1 : (Fin n → α) → ENNReal) (S ∘ π)) =
        ((fun S : Fin n → α => S ∘ π) ⁻¹' B).indicator 1 := by
      funext S; simp [Set.indicator]
    rw [this, lintegral_indicator_one hm, h1]
  have h3 : ∫⁻ S, ∑ π : Equiv.Perm (Fin n), B.indicator (1 : (Fin n → α) → ENNReal) (S ∘ π) ∂μ =
      (n.factorial : ENNReal) * μ B := by
    rw [lintegral_finset_sum]
    · simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
    · intro π _
      exact (measurable_one.indicator hB).comp (pi_comp_perm P n π).measurable
  have h4 : ∀ S : Fin n → α, ∑ π : Equiv.Perm (Fin n), B.indicator (1 : (Fin n → α) → ENNReal) (S ∘ π) ≤
      ENNReal.ofReal (a * (n.factorial : ℝ)) := by
    intro S
    have : ∑ π : Equiv.Perm (Fin n), B.indicator (1 : (Fin n → α) → ENNReal) (S ∘ π) =
        ((Finset.univ.filter (fun π : Equiv.Perm (Fin n) => S ∘ π ∈ B)).card : ENNReal) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun π : Equiv.Perm (Fin n) => S ∘ π ∈ B)]
      rw [Finset.sum_eq_zero (s := Finset.univ.filter (fun π : Equiv.Perm (Fin n) => ¬ S ∘ π ∈ B))
        (fun π hπ => by simp at hπ; simp [Set.indicator, hπ])]
      rw [add_zero, Finset.sum_congr rfl (g := fun _ => (1 : ENNReal))
        (fun π hπ => by simp at hπ; simp [Set.indicator, hπ])]
      simp
    rw [this, ← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hcount S)
  have h5 : (n.factorial : ENNReal) * μ B ≤ ENNReal.ofReal (a * (n.factorial : ℝ)) := by
    rw [← h3]
    calc _ ≤ ∫⁻ _S, ENNReal.ofReal (a * (n.factorial : ℝ)) ∂μ := lintegral_mono h4
      _ = _ := by simp
  have hf : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h6 : ENNReal.ofReal (a * (n.factorial : ℝ)) = (n.factorial : ENNReal) * ENNReal.ofReal a := by
    rw [mul_comm, ENNReal.ofReal_mul hf.le, ENNReal.ofReal_natCast]
  rw [h6] at h5
  have hne : (n.factorial : ENNReal) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hnt : (n.factorial : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  exact (ENNReal.mul_le_mul_iff_right hne hnt).mp h5 |>.trans le_rfl

end OptimalAgnosticPAC.Dev.L31
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L31
open OptimalAgnosticPAC.Learner

section
variable {X : Type} [MeasurableSpace X]

theorem sum_psi {q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ} (h : X → Bool) (k : ℕ) (lam c : ℝ)
    (V : Fin (2 * k) → X × Bool) :
    ∑ t : Fin (2 * k), psi q h k lam c t (pre V t) =
      lam * excessLossSum q h k V - (k : ℝ) * c := by
  have e : ∀ t : Fin (2 * k), psi q h k lam c t (pre V t) =
      if k ≤ t.val then lam * excessLoss q h V t - c else 0 := by
    intro t
    simp only [psi, wf, Dl, excessLoss]
    rfl
  simp only [e]
  rw [← Finset.sum_filter]
  unfold excessLossSum
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, L32.card_suffix, nsmul_eq_mul]

theorem tail_pt {H : Set (X → Bool)} {d : ℕ} (hd : 1 ≤ d)
    {q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ} (hq : IsLOOScore H d q)
    {h : X → Bool} (hh : h ∈ H) {k : ℕ} (hk : 1 ≤ k) (L ℓ δ : ℝ) (hδ0 : 0 < δ) (hℓδ : ℓ = Real.log (1 / δ))
    (hL : 0 ≤ L) (hℓ : 0 < ℓ)
    (S : Fin (2 * k) → X × Bool) (hS : (cnt h S : ℝ) ≤ 4 * k * L + 2 * ℓ) :
    ((Finset.univ.filter (fun π : Equiv.Perm (Fin (2 * k)) =>
      8200 * (Real.sqrt (L * ((d : ℝ) + ℓ) / (k : ℝ)) + ((d : ℝ) + ℓ) / (k : ℝ)) <
        (1 / (k : ℝ)) * max (excessLossSum q h k (S ∘ π)) 0)).card : ℝ) ≤
      δ * ((2 * k).factorial : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set N0 := 4 * (k : ℝ) * L + 2 * ℓ with hN0
  obtain ⟨lam, hl0, hl1, hB⟩ := num_main d k hd hk L ℓ hL hℓ
  set c := lam * muC d N0 k + (3 / 4) * lam ^ 2 * vC d N0 k with hc
  have hexp := perm_exp (psi q h k lam c) (fun n T => (cnt h T : ℝ) ≤ N0)
    (fun n T i hT => le_trans (by exact_mod_cast cnt_del h T i) hT)
    (by
      intro t U σ z
      simp only [psi_snoc, wf, Dl]
      rw [hq.symm t U σ])
    (by
      intro t T hT
      have := step_C hd hq hh hk hl0 hl1 t T hT
      simpa only [psi_snoc] using this)
    (2 * k) S hS
  set F := Finset.univ.filter (fun π : Equiv.Perm (Fin (2 * k)) =>
      8200 * (Real.sqrt (L * ((d : ℝ) + ℓ) / (k : ℝ)) + ((d : ℝ) + ℓ) / (k : ℝ)) <
        (1 / (k : ℝ)) * max (excessLossSum q h k (S ∘ π)) 0) with hF
  have hbad : ∀ π ∈ F, 1 / δ ≤ Real.exp (∑ t : Fin (2 * k), psi q h k lam c t (pre (S ∘ π) t)) := by
    intro π hπ
    simp only [hF, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    rw [sum_psi]
    set E := excessLossSum q h k (S ∘ π)
    have hB' : muC d N0 k + (3 / 4) * lam * vC d N0 k + ℓ / (lam * k) < (1 / (k : ℝ)) * max E 0 :=
      lt_of_le_of_lt hB hπ
    have hpos : 0 < ℓ / (lam * k) := by positivity
    have hmu0 : 0 ≤ muC d N0 k := by unfold muC; positivity
    have hv0 : 0 ≤ vC d N0 k := by unfold vC muC; have : 0 ≤ N0 := by rw [hN0]; positivity
                                   positivity
    have hm : (k : ℝ) * (muC d N0 k + (3 / 4) * lam * vC d N0 k + ℓ / (lam * k)) < max E 0 := by
      have := mul_lt_mul_of_pos_left hB' hkR
      rwa [← mul_assoc, mul_one_div_cancel hkR.ne', one_mul] at this
    have hkb : 0 < (k : ℝ) * (muC d N0 k + (3 / 4) * lam * vC d N0 k + ℓ / (lam * k)) := by
      positivity
    have hE : (k : ℝ) * (muC d N0 k + (3 / 4) * lam * vC d N0 k + ℓ / (lam * k)) < E := by
      rcases le_total E 0 with h0 | h0
      · rw [max_eq_right h0] at hm; linarith
      · rw [max_eq_left h0] at hm; exact hm
    have h2 := mul_lt_mul_of_pos_left hE hl0
    have e : lam * ((k : ℝ) * (muC d N0 k + (3 / 4) * lam * vC d N0 k + ℓ / (lam * k))) =
        (k : ℝ) * c + ℓ := by
      rw [hc]; field_simp
    rw [e] at h2
    have h3 : ℓ < lam * E - (k : ℝ) * c := by linarith
    calc 1 / δ = Real.exp ℓ := by rw [hℓδ, Real.exp_log (by positivity)]
      _ ≤ _ := (Real.exp_lt_exp.mpr h3).le
  have h1 : (F.card : ℝ) * (1 / δ) ≤ ((2 * k).factorial : ℝ) := by
    calc (F.card : ℝ) * (1 / δ) = ∑ _π ∈ F, (1 / δ) := by simp
      _ ≤ ∑ π ∈ F, Real.exp (∑ t : Fin (2 * k), psi q h k lam c t (pre (S ∘ π) t)) :=
          Finset.sum_le_sum hbad
      _ ≤ ∑ π : Equiv.Perm (Fin (2 * k)), Real.exp (∑ t : Fin (2 * k), psi q h k lam c t (pre (S ∘ π) t)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => (Real.exp_pos _).le)
      _ ≤ _ := hexp
  have := mul_le_mul_of_nonneg_left h1 hδ0.le
  calc (F.card : ℝ) = δ * ((F.card : ℝ) * (1 / δ)) := by field_simp
    _ ≤ _ := this

end
end OptimalAgnosticPAC.Dev.L31
end

section
open MeasureTheory
open scoped Classical
namespace OptimalAgnosticPAC.Dev.L31
open OptimalAgnosticPAC.Learner

section
variable {X : Type} [MeasurableSpace X]

theorem cnt_perm {n : ℕ} (h : X → Bool) (S : Fin n → X × Bool) (π : Equiv.Perm (Fin n)) :
    cnt h (S ∘ π) = cnt h S := by
  unfold cnt
  exact Finset.card_equiv π (by intro i; simp)

theorem cnt_meas (h : X → Bool) (hh : Measurable h) (n : ℕ) :
    Measurable (fun S : Fin n → X × Bool => (cnt h S : ℝ)) := by
  have : ∀ S : Fin n → X × Bool, (cnt h S : ℝ) = ∑ i, (if h (S i).1 ≠ (S i).2 then (1 : ℝ) else 0) := by
    intro S; simp only [cnt]; rw [Finset.sum_boole]
  simp only [this]
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact Measurable.ite ((L32.meas_ind h hh).preimage (measurable_pi_apply i)) measurable_const measurable_const

theorem wf_meas {H : Set (X → Bool)} {d : ℕ}
    {q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ} (hq : IsLOOScore H d q)
    {h : X → Bool} (hh : Measurable h) (k : ℕ) (lam c : ℝ) (t : ℕ) :
    Measurable (fun p : (Fin t → X × Bool) × (X × Bool) => wf q h k lam c t p.1 p.2) := by
  unfold wf
  by_cases hkt : k ≤ t
  · simp only [hkt, if_true]
    have hI : Measurable (fun p : (Fin t → X × Bool) × (X × Bool) =>
        (if h p.2.1 ≠ p.2.2 then (1 : ℝ) else 0)) :=
      Measurable.ite ((L32.meas_ind h hh).preimage measurable_snd) measurable_const measurable_const
    exact ((L32.meas_joint H d q hq t).sub hI |>.const_mul lam).sub measurable_const
  · simp only [hkt, if_false]; exact measurable_const

theorem els_meas {H : Set (X → Bool)} {d : ℕ}
    {q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ} (hq : IsLOOScore H d q)
    {h : X → Bool} (hh : Measurable h) (k : ℕ) :
    Measurable (fun S : Fin (2 * k) → X × Bool => excessLossSum q h k S) := by
  have e : ∀ S : Fin (2 * k) → X × Bool, excessLossSum q h k S =
      ∑ t : Fin (2 * k), wf q h k 1 0 t (prefixSample S t t.isLt.le) (S t) := by
    intro S
    unfold excessLossSum
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    by_cases hkt : k ≤ t.val <;> simp [wf, Dl, excessLoss, hkt]
  simp only [e]
  exact L32.measurable_sum _ (wf_meas hq hh k 1 0) (2 * k)

theorem chernoff {P : Measure (X × Bool)} [IsProbabilityMeasure P] {h : X → Bool}
    (hh : Measurable h) (k : ℕ) (hk : 1 ≤ k) (δ : ℝ) (hδ0 : 0 < δ) (L ℓ : ℝ) (hLdef : L = risk P h)
    (hℓδ : ℓ = Real.log (1 / δ)) (hL : 0 ≤ L) (hℓ : 0 < ℓ) :
    Measure.pi (fun _ : Fin (2 * k) => P) {S | 4 * (k : ℝ) * L + 2 * ℓ < (cnt h S : ℝ)} ≤
      ENNReal.ofReal δ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set I : X × Bool → ℝ := fun z => if h z.1 ≠ z.2 then 1 else 0 with hIdef
  have hI : Measurable I := Measurable.ite (L32.meas_ind h hh) measurable_const measurable_const
  have hI01 : ∀ z, I z = 0 ∨ I z = 1 := fun z => by simp only [hIdef]; split_ifs <;> simp
  set κ := Real.exp (1 / 2) - 1 with hκ
  have hκ0 : 0 ≤ κ := by have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
  have hκ1 : κ ≤ 0.65 := by
    have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    have h3 := Real.exp_one_lt_d9
    have h4 := Real.exp_pos (1 / 2 : ℝ)
    by_contra hcon
    push Not at hcon
    nlinarith
  set c0 := κ * L with hc0
  set w : (t : ℕ) → (Fin t → X × Bool) → X × Bool → ℝ := fun _ _ z => (1 / 2) * I z - c0 with hw
  have hrisk : L = ∫ z, I z ∂P := by
    have : I = Set.indicator {z : X × Bool | h z.1 ≠ z.2} 1 := by
      funext z; by_cases hz : h z.1 ≠ z.2 <;> simp [hIdef, hz]
    rw [this, integral_indicator_one (L32.meas_ind h hh), hLdef]; rfl
  have hIint : Integrable I P := Integrable.of_bound hI.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun z => by
      rcases hI01 z with h0 | h0 <;> rw [h0] <;> norm_num))
  have h1 : ∀ t s, ∫⁻ z, ENNReal.ofReal (Real.exp (w t s z)) ∂P ≤ 1 := by
    intro t s
    have hpt : ∀ z, Real.exp (w t s z) = Real.exp (-c0) * (1 + κ * I z) := by
      intro z
      simp only [hw]
      rcases hI01 z with h0 | h0
      · rw [h0]; simp
      · rw [h0, show (1 / 2 : ℝ) * 1 - c0 = (1 / 2) + (-c0) by ring, Real.exp_add, hκ]; ring
    have hint : Integrable (fun z => Real.exp (-c0) * (1 + κ * I z)) P :=
      ((integrable_const 1).add (hIint.const_mul κ)).const_mul _
    have hnn : 0 ≤ᵐ[P] fun z => Real.exp (-c0) * (1 + κ * I z) :=
      Filter.Eventually.of_forall (fun z => by
        have : 0 ≤ I z := by rcases hI01 z with h0 | h0 <;> rw [h0] <;> norm_num
        have := Real.exp_pos (-c0); positivity)
    calc ∫⁻ z, ENNReal.ofReal (Real.exp (w t s z)) ∂P
        = ∫⁻ z, ENNReal.ofReal (Real.exp (-c0) * (1 + κ * I z)) ∂P := by simp only [hpt]
      _ = ENNReal.ofReal (∫ z, Real.exp (-c0) * (1 + κ * I z) ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
      _ ≤ 1 := by
          rw [integral_const_mul, integral_add (integrable_const 1) (hIint.const_mul κ),
            integral_const_mul, ← hrisk]
          simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
          apply ENNReal.ofReal_le_one.mpr
          have := Real.add_one_le_exp (κ * L)
          have h4 : Real.exp (-c0) * Real.exp c0 = 1 := by rw [← Real.exp_add]; simp
          rw [hc0] at h4 ⊢
          nlinarith [Real.exp_pos (-(κ * L))]
  have hwm : ∀ t, Measurable (fun p : (Fin t → X × Bool) × (X × Bool) => w t p.1 p.2) := fun t =>
    ((hI.comp measurable_snd).const_mul (1 / 2)).sub measurable_const
  have hexp := L32.exp_sum_le P w hwm h1 (2 * k)
  set G : (Fin (2 * k) → X × Bool) → ℝ := fun S =>
    ∑ t : Fin (2 * k), w t (prefixSample S t t.isLt.le) (S t) with hG
  have hGeq : ∀ S : Fin (2 * k) → X × Bool, G S = (1 / 2) * (cnt h S : ℝ) - 2 * k * c0 := by
    intro S
    simp only [hG, hw, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : (cnt h S : ℝ) = ∑ i, I (S i) := by simp only [cnt, hIdef]; rw [Finset.sum_boole]
    rw [this]; push_cast; ring
  have hGm : Measurable G := L32.measurable_sum _ hwm (2 * k)
  have hFm : Measurable (fun S => ENNReal.ofReal (Real.exp (G S))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hGm)
  set ε : ENNReal := ENNReal.ofReal (1 / δ) with hε
  have hsub : {S : Fin (2 * k) → X × Bool | 4 * (k : ℝ) * L + 2 * ℓ < (cnt h S : ℝ)} ⊆
      {S | ε ≤ ENNReal.ofReal (Real.exp (G S))} := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS
    have : ℓ ≤ G S := by
      rw [hGeq]
      have : 2 * (k : ℝ) * c0 ≤ 2 * k * (0.65 * L) := by
        rw [hc0]; gcongr
      nlinarith
    simp only [Set.mem_setOf_eq, hε]
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.exp_log (show 0 < 1 / δ by positivity), ← hℓδ]
    exact Real.exp_le_exp.mpr this
  have hmk := mul_meas_ge_le_lintegral₀ (μ := Measure.pi (fun _ : Fin (2 * k) => P))
    hFm.aemeasurable ε
  have hmk' : ε * (Measure.pi (fun _ : Fin (2 * k) => P))
      {S | ε ≤ ENNReal.ofReal (Real.exp (G S))} ≤ 1 := hmk.trans hexp
  refine (measure_mono hsub).trans ?_
  have hεδ : ENNReal.ofReal δ * ε = 1 := by
    rw [hε, ← ENNReal.ofReal_mul hδ0.le]
    rw [mul_one_div_cancel hδ0.ne']; simp
  calc (Measure.pi (fun _ : Fin (2 * k) => P)) {S | ε ≤ ENNReal.ofReal (Real.exp (G S))}
      = ENNReal.ofReal δ * (ε * (Measure.pi (fun _ : Fin (2 * k) => P))
          {S | ε ≤ ENNReal.ofReal (Real.exp (G S))}) := by
        rw [← mul_assoc, hεδ, one_mul]
    _ ≤ ENNReal.ofReal δ * 1 := by gcongr
    _ = _ := mul_one _

end
end OptimalAgnosticPAC.Dev.L31

namespace OptimalAgnosticPAC.Learner
open OptimalAgnosticPAC.Dev.L31

theorem chk_lemma_3_1 {X : Type} [MeasurableSpace X] (H : Set (X → Bool)) (d : ℕ) (hd : 1 ≤ d)
    (hVC : HighDimProb.Chaining.vcDim H ≤ (d : ℕ∞))
    (hmeas : ∀ h ∈ H, Measurable h)
    (q : (m : ℕ) → (Fin m → X × Bool) → X → ℝ) (hq : IsLOOScore H d q)
    (P : Measure (X × Bool)) [IsProbabilityMeasure P]
    (k : ℕ) (hk : 1 ≤ k) (h : X → Bool) (hh : h ∈ H)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 3) :
    sampleLaw P (2 * k)
      {S | 8200 * (Real.sqrt (risk P h * ((d : ℝ) + Real.log (1 / δ)) / (k : ℝ)) +
            ((d : ℝ) + Real.log (1 / δ)) / (k : ℝ)) <
          (1 / (k : ℝ)) * max (excessLossSum q h k S) 0} ≤
      ENNReal.ofReal (2 * δ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hℓ : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hδ0]; linarith
  have hL0 : 0 ≤ risk P h := measureReal_nonneg
  have hhm := hmeas h hh
  set ℓ := Real.log (1 / δ) with hℓdef
  set L := risk P h with hLdef
  set μ := Measure.pi (fun _ : Fin (2 * k) => P) with hμ
  set A : Set (Fin (2 * k) → X × Bool) :=
    {S | 8200 * (Real.sqrt (L * ((d : ℝ) + ℓ) / (k : ℝ)) + ((d : ℝ) + ℓ) / (k : ℝ)) <
          (1 / (k : ℝ)) * max (excessLossSum q h k S) 0} with hA
  set Gd : Set (Fin (2 * k) → X × Bool) := {S | (cnt h S : ℝ) ≤ 4 * (k : ℝ) * L + 2 * ℓ} with hGd
  have hAm : MeasurableSet A :=
    measurableSet_lt measurable_const
      ((((els_meas hq hhm k).max measurable_const)).const_mul _)
  have hGm : MeasurableSet Gd := measurableSet_le (cnt_meas h hhm _) measurable_const
  have hch := chernoff (P := P) hhm k hk δ hδ0 L ℓ rfl rfl hL0 hℓ
  have hAG : μ (A ∩ Gd) ≤ ENNReal.ofReal δ := by
    refine perm_avg P (2 * k) (A ∩ Gd) (hAm.inter hGm) δ (fun S => ?_)
    by_cases hS : S ∈ Gd
    · refine le_trans ?_ (tail_pt hd hq hh hk L ℓ δ hδ0 rfl hL0 hℓ S hS)
      refine Nat.cast_le.mpr (Finset.card_le_card (fun π hπ => ?_))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      exact hπ.1
    · refine le_trans (le_of_eq ?_) (by positivity : (0 : ℝ) ≤ δ * ((2 * k).factorial : ℝ))
      norm_cast
      refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem (fun π hπ' => hS ?_))
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ'
      have := hπ'.2
      simp only [hGd, Set.mem_setOf_eq, cnt_perm] at this ⊢
      exact this
  have hsub : A ⊆ (A ∩ Gd) ∪ {S | 4 * (k : ℝ) * L + 2 * ℓ < (cnt h S : ℝ)} := by
    intro S hS
    by_cases hG : S ∈ Gd
    · exact Or.inl ⟨hS, hG⟩
    · refine Or.inr ?_
      simp only [hGd, Set.mem_setOf_eq, not_le] at hG ⊢
      exact hG
  unfold sampleLaw
  calc μ A ≤ μ ((A ∩ Gd) ∪ {S | 4 * (k : ℝ) * L + 2 * ℓ < (cnt h S : ℝ)}) := measure_mono hsub
    _ ≤ μ (A ∩ Gd) + μ {S | 4 * (k : ℝ) * L + 2 * ℓ < (cnt h S : ℝ)} := measure_union_le _ _
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := add_le_add hAG hch
    _ = ENNReal.ofReal (2 * δ) := by
        rw [← ENNReal.ofReal_add hδ0.le hδ0.le]; ring_nf

end OptimalAgnosticPAC.Learner
end

theorem solution : type_of% @OptimalAgnosticPAC.Learner.chk_lemma_3_1 := @OptimalAgnosticPAC.Learner.chk_lemma_3_1
