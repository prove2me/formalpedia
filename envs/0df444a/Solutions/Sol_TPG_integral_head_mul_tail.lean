-- Prove2me | solution 1 for TPG.integral_head_mul_tail
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T03:56:24.567557+00:00
-- url     : https://prove2.me/submissions/03e917cc-c6c1-43c9-83fb-f2fdaea2b550

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Markov
import Theorems.Thm_TPG_integral_trajLaw

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

/-! ### Path-weight factorization (finite algebra) -/

/-- The only transition factor linking the head block to the tail block is the one from the last
head time to the first tail time; written as a sum over the state at the first tail time. -/
private lemma hmt_cross {S : Type} [Fintype S] [DecidableEq S] (E : Env S) (m n : ℕ)
    (xh : Fin (m + 1) → S) (zh : Fin (m + 1) → Bool) (xt : Fin n → S) :
    (∏ i : Fin (m + 1), ∏ j : Fin n,
        if (i : ℕ) + 1 = m + 1 + (j : ℕ) then E.P (i : ℕ) (zh i) (xh i) (xt j) else 1)
      = ∑ a : S, E.P m (zh (Fin.last m)) (xh (Fin.last m)) a
          * ∏ j : Fin n, if (j : ℕ) = 0 then (if xt j = a then (1 : ℝ) else 0) else 1 := by
  cases n with
  | zero => simp [E.P_row_sum]
  | succ k =>
    rw [Fin.prod_univ_castSucc]
    have h1 : ∏ i : Fin m, ∏ j : Fin (k + 1),
        (if ((Fin.castSucc i : Fin (m + 1)) : ℕ) + 1 = m + 1 + (j : ℕ)
          then E.P ((Fin.castSucc i : Fin (m + 1)) : ℕ) (zh (Fin.castSucc i))
            (xh (Fin.castSucc i)) (xt j) else 1) = 1 :=
      Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => if_neg (by
        have := i.isLt
        simp only [Fin.val_castSucc]
        omega)
    rw [h1, one_mul, Fin.prod_univ_succ]
    have h2 : ∏ j : Fin k,
        (if ((Fin.last m : Fin (m + 1)) : ℕ) + 1 = m + 1 + ((Fin.succ j : Fin (k + 1)) : ℕ)
          then E.P ((Fin.last m : Fin (m + 1)) : ℕ) (zh (Fin.last m)) (xh (Fin.last m))
            (xt (Fin.succ j)) else 1) = 1 :=
      Finset.prod_eq_one fun j _ => if_neg (by
        simp only [Fin.val_last, Fin.val_succ]
        omega)
    rw [h2, mul_one]
    have h3 : ∀ a : S, ∏ j : Fin (k + 1),
        (if (j : ℕ) = 0 then (if xt j = a then (1 : ℝ) else 0) else 1)
          = if xt 0 = a then 1 else 0 := by
      intro a
      rw [Fin.prod_univ_succ]
      simp
    simp only [h3]
    simp

/-- Markov factorization of the path weight along an appended path. -/
private lemma hmt_pathWeight_append {S : Type} [Fintype S] [DecidableEq S] (E : Env S)
    (m n : ℕ) (q : ℕ → ℝ)
    (xh : Fin (m + 1) → S) (zh : Fin (m + 1) → Bool) (xt : Fin n → S) (zt : Fin n → Bool) :
    E.pathWeight (m + 1 + n) q (Fin.append xh xt) (Fin.append zh zt)
      = E.pathWeight (m + 1) q xh zh
          * ∑ a : S, E.P m (zh (Fin.last m)) (xh (Fin.last m)) a
              * (E.shift (m + 1) a).pathWeight n (fun t => q (m + 1 + t)) xt zt := by
  have hρ : ∏ t : Fin (m + 1 + n), (if (t : ℕ) = 0 then E.ρ (Fin.append xh xt t) else 1)
      = ∏ t : Fin (m + 1), (if (t : ℕ) = 0 then E.ρ (xh t) else 1) := by
    rw [Fin.prod_univ_add]
    have h1 : ∏ j : Fin n, (if ((Fin.natAdd (m + 1) j : Fin (m + 1 + n)) : ℕ) = 0
        then E.ρ (Fin.append xh xt (Fin.natAdd (m + 1) j)) else 1) = 1 :=
      Finset.prod_eq_one fun j _ => if_neg (by
        simp only [Fin.val_natAdd]
        omega)
    rw [h1, mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Fin.append_left, Fin.val_castAdd]
  have hact : ∏ t : Fin (m + 1 + n),
        (if Fin.append zh zt t then q (t : ℕ) else 1 - q (t : ℕ))
      = (∏ t : Fin (m + 1), if zh t then q (t : ℕ) else 1 - q (t : ℕ))
        * ∏ t : Fin n, if zt t then q (m + 1 + (t : ℕ)) else 1 - q (m + 1 + (t : ℕ)) := by
    rw [Fin.prod_univ_add]
    simp only [Fin.append_left, Fin.append_right, Fin.val_castAdd, Fin.val_natAdd]
  have htr : ∏ s : Fin (m + 1 + n), ∏ t : Fin (m + 1 + n),
        (if (s : ℕ) + 1 = (t : ℕ) then
          E.P (s : ℕ) (Fin.append zh zt s) (Fin.append xh xt s) (Fin.append xh xt t) else 1)
      = (∏ s : Fin (m + 1), ∏ t : Fin (m + 1),
            if (s : ℕ) + 1 = (t : ℕ) then E.P (s : ℕ) (zh s) (xh s) (xh t) else 1)
        * (∏ i : Fin (m + 1), ∏ j : Fin n,
            if (i : ℕ) + 1 = m + 1 + (j : ℕ) then E.P (i : ℕ) (zh i) (xh i) (xt j) else 1)
        * (∏ s : Fin n, ∏ t : Fin n,
            if (s : ℕ) + 1 = (t : ℕ)
              then E.P (m + 1 + (s : ℕ)) (zt s) (xt s) (xt t) else 1) := by
    have hsplit : ∀ g : Fin (m + 1 + n) → ℝ, ∏ t : Fin (m + 1 + n), g t
        = (∏ i : Fin (m + 1), g (Fin.castAdd n i)) * ∏ j : Fin n, g (Fin.natAdd (m + 1) j) :=
      fun g => Fin.prod_univ_add g
    simp only [hsplit, Fin.append_left, Fin.append_right, Fin.val_castAdd,
      Fin.val_natAdd, Finset.prod_mul_distrib]
    have h1 : ∏ j : Fin n, ∏ i : Fin (m + 1),
        (if m + 1 + (j : ℕ) + 1 = (i : ℕ)
          then E.P (m + 1 + (j : ℕ)) (zt j) (xt j) (xh i) else 1) = 1 :=
      Finset.prod_eq_one fun j _ => Finset.prod_eq_one fun i _ => if_neg (by
        have := i.isLt
        omega)
    have h2 : ∏ s : Fin n, ∏ t : Fin n,
        (if m + 1 + (s : ℕ) + 1 = m + 1 + (t : ℕ)
          then E.P (m + 1 + (s : ℕ)) (zt s) (xt s) (xt t) else 1)
        = ∏ s : Fin n, ∏ t : Fin n,
          (if (s : ℕ) + 1 = (t : ℕ)
            then E.P (m + 1 + (s : ℕ)) (zt s) (xt s) (xt t) else 1) :=
      Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun t _ =>
        if_congr (by omega) rfl rfl
    rw [h1, h2, one_mul]
  have hsh : ∀ a : S, (E.shift (m + 1) a).pathWeight n (fun t => q (m + 1 + t)) xt zt
      = (∏ j : Fin n, if (j : ℕ) = 0 then (if xt j = a then (1 : ℝ) else 0) else 1)
        * (∏ s : Fin n, ∏ t : Fin n,
            if (s : ℕ) + 1 = (t : ℕ)
              then E.P (m + 1 + (s : ℕ)) (zt s) (xt s) (xt t) else 1)
        * ∏ t : Fin n, if zt t then q (m + 1 + (t : ℕ)) else 1 - q (m + 1 + (t : ℕ)) :=
    fun a => rfl
  simp only [hsh]
  unfold Env.pathWeight
  rw [hρ, htr, hact, hmt_cross E m n xh zh xt]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-! ### Splitting a finite product measure -/

private lemma hmt_measurable_append (m n : ℕ) :
    Measurable (fun p : (Fin m → ℝ) × (Fin n → ℝ) => (Fin.append p.1 p.2 : Fin (m + n) → ℝ)) := by
  refine measurable_pi_lambda _ fun i => ?_
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · simp only [Fin.append_left]
    exact (measurable_pi_apply i).comp measurable_fst
  · simp only [Fin.append_right]
    exact (measurable_pi_apply j).comp measurable_snd

/-- A product measure over `Fin (m + n)` is the image of the product of the two block product
measures under concatenation. -/
private lemma hmt_pi_append (m n : ℕ) (μ : Fin (m + n) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] :
    Measure.pi μ = ((Measure.pi fun i : Fin m => μ (Fin.castAdd n i)).prod
        (Measure.pi fun j : Fin n => μ (Fin.natAdd m j))).map
          (fun p : (Fin m → ℝ) × (Fin n → ℝ) => (Fin.append p.1 p.2 : Fin (m + n) → ℝ)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (hmt_measurable_append m n) (MeasurableSet.univ_pi hs)]
  have hpre : (fun p : (Fin m → ℝ) × (Fin n → ℝ) => (Fin.append p.1 p.2 : Fin (m + n) → ℝ))
        ⁻¹' (Set.pi Set.univ s)
      = (Set.pi Set.univ fun i : Fin m => s (Fin.castAdd n i))
          ×ˢ (Set.pi Set.univ fun j : Fin n => s (Fin.natAdd m j)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun j => ?_⟩
      · simpa only [Fin.append_left] using h (Fin.castAdd n i)
      · simpa only [Fin.append_right] using h (Fin.natAdd m j)
    · rintro ⟨h1, h2⟩ i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using h1 i
      · simpa only [Fin.append_right] using h2 j
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, Fin.prod_univ_add]

/-- Under a product measure over `Fin (m + n)`, a function of the first `m` coordinates and a
function of the last `n` coordinates are independent. -/
private lemma hmt_integral_pi_split (m n : ℕ) (μ : Fin (m + n) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : (Fin m → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ) (hf : Measurable f) (hg : Measurable g) :
    ∫ y, f (fun i => y (Fin.castAdd n i)) * g (fun j => y (Fin.natAdd m j)) ∂(Measure.pi μ)
      = (∫ u, f u ∂(Measure.pi fun i : Fin m => μ (Fin.castAdd n i)))
        * ∫ v, g v ∂(Measure.pi fun j : Fin n => μ (Fin.natAdd m j)) := by
  have hm : Measurable (fun y : Fin (m + n) → ℝ =>
      f (fun i => y (Fin.castAdd n i)) * g (fun j => y (Fin.natAdd m j))) :=
    (hf.comp (measurable_pi_lambda _ fun i => measurable_pi_apply _)).mul
      (hg.comp (measurable_pi_lambda _ fun j => measurable_pi_apply _))
  rw [hmt_pi_append m n μ,
    integral_map (hmt_measurable_append m n).aemeasurable hm.aestronglyMeasurable]
  simp only [Fin.append_left, Fin.append_right]
  exact integral_prod_mul f g

/-! ### Integrals against the trajectory law -/

private lemma hmt_measurable_embedPath {S : Type} [MeasurableSpace S] {T : ℕ}
    (x : Fin T → S) (z : Fin T → Bool) :
    Measurable (embedPath x z) := by
  unfold embedPath
  exact measurable_pi_lambda _ fun t =>
    measurable_const.prodMk (measurable_const.prodMk (measurable_pi_apply t))

section traj

variable {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]

/-- `integral_trajLaw` for bounded measurable functions. -/
private lemma hmt_integral_bdd (E : Env S) (T : ℕ) (q : ℕ → ℝ)
    (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1) (F : Traj S T → ℝ) (hF : Measurable F) (C : ℝ)
    (hFb : ∀ ω, |F ω| ≤ C) :
    ∫ ω, F ω ∂(E.trajLaw T q)
      = ∑ p : (Fin T → S) × (Fin T → Bool),
          E.pathWeight T q p.1 p.2 * ∫ y, F (embedPath p.1 p.2 y) ∂(E.rewardLaw p.1 p.2) := by
  refine (integral_trajLaw E T q hq F hF fun p => ?_).2
  have hm : Measurable (fun y : Fin T → ℝ => F (embedPath p.1 p.2 y)) :=
    hF.comp (hmt_measurable_embedPath p.1 p.2)
  have : IsProbabilityMeasure (E.rewardLaw p.1 p.2) := by
    unfold Env.rewardLaw; infer_instance
  exact Integrable.of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hFb _)

/-- Reindexing a sum over paths of length `m + n` by (head path, tail path). -/
private lemma hmt_sum_append {α β : Type} [Fintype α] [Fintype β] (m n : ℕ)
    (f : (Fin (m + n) → α) × (Fin (m + n) → β) → ℝ) :
    ∑ p, f p = ∑ ph : (Fin m → α) × (Fin m → β), ∑ pt : (Fin n → α) × (Fin n → β),
        f (Fin.append ph.1 pt.1, Fin.append ph.2 pt.2) := by
  rw [← Fintype.sum_prod_type',
    ← ((Equiv.prodProdProdComm _ _ _ _).trans
      ((Fin.appendEquiv m n).prodCongr (Fin.appendEquiv m n))).sum_comp f]
  rfl

/-- The left-hand side as a double sum over head and tail paths. -/
private lemma hmt_lhs (E : Env S) (m n : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (F : Traj S m → ℝ) (G : Traj S n → ℝ) (hF : Measurable F) (hG : Measurable G)
    (CF CG : ℝ) (hFb : ∀ ω, |F ω| ≤ CF) (hGb : ∀ ω, |G ω| ≤ CG) :
    ∫ ω, F (headTraj m n ω) * G (tailTraj m n ω) ∂(E.trajLaw (m + n) q)
      = ∑ ph : (Fin m → S) × (Fin m → Bool), ∑ pt : (Fin n → S) × (Fin n → Bool),
          E.pathWeight (m + n) q (Fin.append ph.1 pt.1) (Fin.append ph.2 pt.2)
            * ((∫ y, F (embedPath ph.1 ph.2 y) ∂(E.rewardLaw ph.1 ph.2))
              * ∫ y, G (embedPath pt.1 pt.2 y) ∂(E.rewardLaw pt.1 pt.2)) := by
  have hhead : Measurable (headTraj (S := S) m n) := by
    unfold headTraj
    exact measurable_pi_lambda _ fun i => measurable_pi_apply _
  have htail : Measurable (tailTraj (S := S) m n) := by
    unfold tailTraj
    exact measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hH : Measurable (fun ω : Traj S (m + n) => F (headTraj m n ω) * G (tailTraj m n ω)) :=
    (hF.comp hhead).mul (hG.comp htail)
  have hb : ∀ ω : Traj S (m + n), |F (headTraj m n ω) * G (tailTraj m n ω)| ≤ |CF| * |CG| := by
    intro ω
    rw [abs_mul]
    exact mul_le_mul ((hFb _).trans (le_abs_self _)) ((hGb _).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  rw [hmt_integral_bdd E (m + n) q hq _ hH _ hb, hmt_sum_append]
  refine Finset.sum_congr rfl fun ph _ => Finset.sum_congr rfl fun pt _ => ?_
  congr 1
  have key := hmt_integral_pi_split m n
    (fun t => E.R (Fin.append ph.1 pt.1 t) (Fin.append ph.2 pt.2 t))
    (fun u => F (embedPath ph.1 ph.2 u)) (fun v => G (embedPath pt.1 pt.2 v))
    (hF.comp (hmt_measurable_embedPath ph.1 ph.2))
    (hG.comp (hmt_measurable_embedPath pt.1 pt.2))
  have h1 : ∀ y : Fin (m + n) → ℝ,
      headTraj m n (embedPath (Fin.append ph.1 pt.1) (Fin.append ph.2 pt.2) y)
        = embedPath ph.1 ph.2 (fun i => y (Fin.castAdd n i)) := by
    intro y
    funext i
    simp only [headTraj, embedPath, Fin.append_left]
  have h2 : ∀ y : Fin (m + n) → ℝ,
      tailTraj m n (embedPath (Fin.append ph.1 pt.1) (Fin.append ph.2 pt.2) y)
        = embedPath pt.1 pt.2 (fun j => y (Fin.natAdd m j)) := by
    intro y
    funext j
    simp only [tailTraj, embedPath, Fin.append_right]
  simp only [h1, h2]
  simp only [Env.rewardLaw, Fin.append_left, Fin.append_right] at key ⊢
  exact key

/-- The head integral of the right-hand side as a sum over head paths. -/
private lemma hmt_rhs1 (E : Env S) (m : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (F : Traj S (m + 1) → ℝ) (hF : Measurable F) (CF : ℝ) (hFb : ∀ ω, |F ω| ≤ CF) (a : S) :
    ∫ ω, F ω * E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a ∂(E.trajLaw (m + 1) q)
      = ∑ ph : (Fin (m + 1) → S) × (Fin (m + 1) → Bool),
          E.pathWeight (m + 1) q ph.1 ph.2
            * ((∫ y, F (embedPath ph.1 ph.2 y) ∂(E.rewardLaw ph.1 ph.2))
              * E.P m (ph.2 (Fin.last m)) (ph.1 (Fin.last m)) a) := by
  have hX : Measurable (fun ω : Traj S (m + 1) => X (Fin.last m) ω) := by
    unfold X
    exact measurable_fst.comp (measurable_pi_apply _)
  have hZ : Measurable (fun ω : Traj S (m + 1) => Z (Fin.last m) ω) := by
    unfold Z
    exact measurable_fst.comp (measurable_snd.comp (measurable_pi_apply _))
  have hP : Measurable (fun ω : Traj S (m + 1) =>
      E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a) :=
    (Measurable.of_discrete (f := fun p : Bool × S => E.P m p.1 p.2 a)).comp (hZ.prodMk hX)
  have hP1 : ∀ (z : Bool) (x : S), E.P m z x a ≤ 1 := by
    intro z x
    rw [← E.P_row_sum m z x]
    exact Finset.single_le_sum (fun i _ => E.P_nonneg m z x i) (Finset.mem_univ a)
  have hb : ∀ ω : Traj S (m + 1),
      |F ω * E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a| ≤ |CF| := by
    intro ω
    rw [abs_mul, abs_of_nonneg (E.P_nonneg _ _ _ _)]
    calc |F ω| * E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a
        ≤ |CF| * 1 := mul_le_mul ((hFb _).trans (le_abs_self _)) (hP1 _ _)
          (E.P_nonneg _ _ _ _) (abs_nonneg _)
      _ = |CF| := mul_one _
  have hFP : Measurable (fun ω : Traj S (m + 1) =>
      F ω * E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a) := hF.mul hP
  rw [hmt_integral_bdd E (m + 1) q hq
    (fun ω : Traj S (m + 1) => F ω * E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a) hFP _ hb]
  refine Finset.sum_congr rfl fun ph _ => ?_
  congr 1
  exact integral_mul_const (E.P m (ph.2 (Fin.last m)) (ph.1 (Fin.last m)) a)
    (fun y => F (embedPath ph.1 ph.2 y))

end traj

theorem solution {S : Type} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (m n : ℕ) (q : ℕ → ℝ) (hq : ∀ t : ℕ, 0 ≤ q t ∧ q t ≤ 1)
    (F : Traj S (m + 1) → ℝ) (G : Traj S n → ℝ) (hF : Measurable F) (hG : Measurable G)
    (CF CG : ℝ) (hFb : ∀ ω, |F ω| ≤ CF) (hGb : ∀ ω, |G ω| ≤ CG) :
    ∫ ω, F (headTraj (m + 1) n ω) * G (tailTraj (m + 1) n ω) ∂(E.trajLaw (m + 1 + n) q)
      = ∑ a : S,
          (∫ ω, F ω * E.P m (Z (Fin.last m) ω) (X (Fin.last m) ω) a ∂(E.trajLaw (m + 1) q))
            * ∫ ω, G ω ∂((E.shift (m + 1) a).trajLaw n (fun t => q (m + 1 + t))) := by
  have hq' : ∀ t : ℕ, 0 ≤ q (m + 1 + t) ∧ q (m + 1 + t) ≤ 1 := fun t => hq _
  have hR2 : ∀ a : S, ∫ ω, G ω ∂((E.shift (m + 1) a).trajLaw n (fun t => q (m + 1 + t)))
      = ∑ pt : (Fin n → S) × (Fin n → Bool),
          (E.shift (m + 1) a).pathWeight n (fun t => q (m + 1 + t)) pt.1 pt.2
            * ∫ y, G (embedPath pt.1 pt.2 y) ∂(E.rewardLaw pt.1 pt.2) :=
    fun a => hmt_integral_bdd (E.shift (m + 1) a) n _ hq' G hG CG hGb
  rw [hmt_lhs E (m + 1) n q hq F G hF hG CF CG hFb hGb]
  simp only [hR2, hmt_rhs1 E m q hq F hF CF hFb, Finset.sum_mul_sum]
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun ph _ => ?_
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun pt _ => ?_
  rw [hmt_pathWeight_append, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring
