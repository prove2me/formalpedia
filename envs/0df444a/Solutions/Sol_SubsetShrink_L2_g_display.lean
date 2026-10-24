-- Prove2me | solution 1 for SubsetShrink.L2.g_display
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T06:07:24.211574+00:00
-- url     : https://prove2.me/submissions/83212ec4-08cb-433d-9622-f3a214cd781d

import Mathlib
import Definitions.Def_SubsetShrink_L2_Model

namespace SubsetShrink.L2.Aux

open SubsetShrink.L2

lemma l2_sq {m : ℕ} (v : Fin m → ℝ) : l2 v ^ 2 = ∑ i, v i ^ 2 := by
  unfold l2
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]

lemma l2_nonneg {m : ℕ} (v : Fin m → ℝ) : 0 ≤ l2 v := Real.sqrt_nonneg _

lemma l2_eq_norm {m : ℕ} (v : Fin m → ℝ) :
    l2 v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin m))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold l2
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [sq_abs]

lemma l2_sub_le {m : ℕ} (a b : Fin m → ℝ) : l2 (a - b) ≤ l2 a + l2 b := by
  rw [l2_eq_norm, l2_eq_norm, l2_eq_norm, WithLp.toLp_sub]
  exact norm_sub_le _ _

lemma l2_add_le {m : ℕ} (a b : Fin m → ℝ) : l2 (a + b) ≤ l2 a + l2 b := by
  rw [l2_eq_norm, l2_eq_norm, l2_eq_norm, WithLp.toLp_add]
  exact norm_add_le _ _

lemma l2_neg {m : ℕ} (a : Fin m → ℝ) : l2 (-a) = l2 a := by
  unfold l2
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  simp

lemma l2_sub_comm {m : ℕ} (a b : Fin m → ℝ) : l2 (a - b) = l2 (b - a) := by
  rw [← neg_sub, l2_neg]

lemma l2_pos {m : ℕ} (a : Fin m → ℝ) (ha : a ≠ 0) : 0 < l2 a := by
  rw [l2_eq_norm]
  apply norm_pos_iff.2
  intro h
  apply ha
  have := congrArg (WithLp.ofLp) h
  simpa using this

/-- `l2 β ≤ l2 (β - βhat) + l2 βhat`. -/
lemma l2_le_sub_add {m : ℕ} (a b : Fin m → ℝ) : l2 a ≤ l2 (a - b) + l2 b := by
  have := l2_add_le (a - b) b
  simpa using this

lemma l0_sub_le {m : ℕ} (a b : Fin m → ℝ) : l0 (a - b) ≤ l0 a + l0 b := by
  unfold l0
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Finset.mem_union] at hi ⊢
  by_contra h
  push Not at h
  exact hi (by rw [h.1, h.2]; ring)

lemma mulVec_sub_resid {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ)
    (βhat β : Fin p → ℝ) :
    X.mulVec (β - βhat) = resid X fstar βhat - resid X fstar β := by
  ext i
  simp only [resid, Matrix.mulVec_sub, Pi.sub_apply]
  ring

lemma l2_mulVec_le {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar : Fin n → ℝ)
    (βhat β : Fin p → ℝ) :
    l2 (X.mulVec (β - βhat)) ≤ l2 (resid X fstar βhat) + l2 (resid X fstar β) := by
  rw [mulVec_sub_resid X fstar βhat β]
  exact l2_sub_le _ _

lemma l2_mulVec_comm {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (βhat β : Fin p → ℝ) :
    l2 (X.mulVec (βhat - β)) = l2 (X.mulVec (β - βhat)) := by
  rw [← neg_sub β βhat, Matrix.mulVec_neg, l2_neg]

/-- The basic inequality (29). -/
lemma basic {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ) (k : ℕ)
    (lam : ℝ) (βhat β : Fin p → ℝ)
    (hbest : IsL2BestSubset X (fun i => fstar i + ε i) k lam βhat) (hβ : β ∈ B0 k) :
    (l2 (fun i => (fstar i + ε i) - X.mulVec βhat i) ^ 2 + lam * l2 βhat ≤
        l2 (fun i => (fstar i + ε i) - X.mulVec β i) ^ 2 + lam * l2 β) ∧
      l2 (resid X fstar βhat) ^ 2 + lam * l2 βhat ≤
        l2 (resid X fstar β) ^ 2 + 2 * dot ε (X.mulVec (βhat - β)) + lam * l2 β := by
  have h1 := hbest.2 β hβ
  refine ⟨h1, ?_⟩
  rw [l2_sq, l2_sq] at h1
  rw [l2_sq, l2_sq]
  have key : ∑ i, (fstar i + ε i - X.mulVec βhat i) ^ 2 -
      ∑ i, (fstar i + ε i - X.mulVec β i) ^ 2 =
      ∑ i, resid X fstar βhat i ^ 2 - ∑ i, resid X fstar β i ^ 2 -
        2 * dot ε (X.mulVec (βhat - β)) := by
    simp only [resid, dot, Matrix.mulVec_sub, Pi.sub_apply, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  linarith

/-- Antitone sums over a finset of naturals are dominated by the initial segment. -/
lemma sum_antitone_le {g : ℕ → ℝ} (hg : Antitone g) (J : Finset ℕ) :
    ∑ j ∈ J, g j ≤ ∑ i ∈ Finset.range J.card, g i := by
  induction J using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have has : a ∉ s := fun h => lt_irrefl _ (ha a h)
    rw [Finset.sum_insert has, Finset.card_insert_of_notMem has, Finset.sum_range_succ]
    have hcard : s.card ≤ a := by
      have hsub : s ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (ha x hx)
      simpa using Finset.card_le_card hsub
    linarith [hg hcard]

/-- `∑_{j=1}^m log(2p/j) ≤ m log(2ep/m)`. -/
lemma sum_log_le (p m : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    ∑ i ∈ Finset.range m, Real.log (2 * (p : ℝ) / ((i : ℝ) + 1)) ≤
      (m : ℝ) * Real.log (2 * Real.exp 1 * (p : ℝ) / (m : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : ∀ i ∈ Finset.range m, Real.log (2 * (p : ℝ) / ((i : ℝ) + 1)) =
      Real.log (2 * (p : ℝ)) - Real.log ((i : ℝ) + 1) := by
    intro i _
    rw [Real.log_div (by positivity) (by positivity)]
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  have h2 : ∑ i ∈ Finset.range m, Real.log ((i : ℝ) + 1) = Real.log (m.factorial : ℝ) := by
    rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod,
      Real.log_prod (fun i _ => by positivity)]
    push_cast
    rfl
  rw [h2]
  have h3 := Real.pow_div_factorial_le_exp (x := (m : ℝ)) (le_of_lt hm0) m
  have hf : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have h4 : Real.log ((m : ℝ) ^ m / (m.factorial : ℝ)) ≤ (m : ℝ) := by
    have := Real.log_le_log (by positivity) h3
    rwa [Real.log_exp] at this
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow] at h4
  have e5 : Real.log (2 * Real.exp 1 * (p : ℝ) / (m : ℝ)) =
      Real.log 2 + 1 + Real.log p - Real.log m := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_exp]
  have e6 : Real.log (2 * (p : ℝ)) = Real.log 2 + Real.log p :=
    Real.log_mul (by positivity) (by positivity)
  rw [e5, e6]
  have e7 : (m : ℝ) * (Real.log 2 + 1 + Real.log p - Real.log m) =
      m * Real.log 2 + m + m * Real.log p - m * Real.log m := by ring
  have e8 : (m : ℝ) * (Real.log 2 + Real.log p) = m * Real.log 2 + m * Real.log p := by ring
  rw [e7, e8]
  linarith

/-- The sorted-sum bound used in Theorem 1's proof: for `‖u‖₀ ≤ m ≤ 2p`,
`∑_j u♯_j √log(2p/j) ≤ √(m log(2ep/m)) ‖u‖`. -/
lemma sortedSum_le {p : ℕ} (u : Fin p → ℝ) (m : ℕ) (hm1 : 1 ≤ m) (hm : m ≤ 2 * p)
    (hu : l0 u ≤ m) :
    sortedSum u ≤ Real.sqrt ((m : ℝ) * Real.log (2 * Real.exp 1 * (p : ℝ) / (m : ℝ))) * l2 u := by
  have hp : 1 ≤ p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  unfold sortedSum
  refine Finset.sup'_le _ _ ?_
  intro π _
  set g : ℕ → ℝ := fun x => Real.log (2 * (p : ℝ) / ((x : ℝ) + 1)) with hg
  have hgnn : ∀ x : ℕ, x < 2 * p → 0 ≤ g x := by
    intro x hx
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    have : (x : ℝ) + 1 ≤ 2 * p := by exact_mod_cast hx
    linarith
  have hganti : Antitone g := by
    intro x y hxy
    simp only [hg]
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : (x : ℝ) ≤ y := by exact_mod_cast hxy
    linarith
  set J := Finset.univ.filter (fun j : Fin p => u (π j) ≠ 0) with hJ
  set w : Fin p → ℝ := fun j => if u (π j) ≠ 0 then Real.sqrt (g j.val) else 0 with hw
  have e1 : ∑ j, |u (π j)| * Real.sqrt (Real.log (2 * (p : ℝ) / ((j.val : ℝ) + 1))) =
      ∑ j, |u (π j)| * w j := by
    refine Finset.sum_congr rfl ?_
    intro j _
    simp only [hw, hg]
    split_ifs with h
    · rfl
    · push Not at h; simp [h]
  rw [e1]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => |u (π j)|) w
  have e2 : ∑ j, |u (π j)| ^ 2 = l2 u ^ 2 := by
    rw [l2_sq]
    simp only [sq_abs]
    exact Equiv.sum_comp π (fun i => u i ^ 2)
  have e3 : ∑ j, w j ^ 2 = ∑ j ∈ J, g j.val := by
    rw [hJ, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp only [hw]
    split_ifs with h
    · rw [Real.sq_sqrt (hgnn _ (by omega))]
    · simp
  have hcardJ : J.card = l0 u := by
    unfold l0
    rw [hJ]
    refine Finset.card_bij (fun j _ => π j) ?_ ?_ ?_
    · intro j hj; simpa using hj
    · intro a _ b _ h; exact π.injective h
    · intro i hi
      refine ⟨π.symm i, ?_, by simp⟩
      simpa using hi
  have e4 : ∑ j ∈ J, g j.val ≤ (m : ℝ) * Real.log (2 * Real.exp 1 * (p : ℝ) / (m : ℝ)) := by
    have h5 : ∑ j ∈ J, g j.val = ∑ x ∈ J.map Fin.valEmbedding, g x := by
      rw [Finset.sum_map]; rfl
    rw [h5]
    refine le_trans (sum_antitone_le hganti _) ?_
    rw [Finset.card_map, hcardJ]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.2 hu) ?_) (sum_log_le p m hm1 hp)
    intro x hx _
    exact hgnn x (by have := Finset.mem_range.1 hx; omega)
  rw [e2, e3] at cs
  have hS : 0 ≤ ∑ j, |u (π j)| * w j := by
    refine Finset.sum_nonneg ?_
    intro j _
    refine mul_nonneg (abs_nonneg _) ?_
    simp only [hw]; split_ifs <;> positivity
  have hT : 0 ≤ ∑ j ∈ J, g j.val := by
    rw [← e3]; exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  calc ∑ j, |u (π j)| * w j
      = Real.sqrt ((∑ j, |u (π j)| * w j) ^ 2) := (Real.sqrt_sq hS).symm
    _ ≤ Real.sqrt (l2 u ^ 2 * ∑ j ∈ J, g j.val) := Real.sqrt_le_sqrt cs
    _ = Real.sqrt (∑ j ∈ J, g j.val) * l2 u := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (l2_nonneg _), mul_comm]
    _ ≤ Real.sqrt ((m : ℝ) * Real.log (2 * Real.exp 1 * (p : ℝ) / (m : ℝ))) * l2 u :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt e4) (l2_nonneg _)

/-- Radicand identity `(2k) log(2ep/(2k)) = 2k log(ep/k)`. -/
lemma rad_eq (p k : ℕ) (hk : 1 ≤ k) :
    ((2 * k : ℕ) : ℝ) * Real.log (2 * Real.exp 1 * (p : ℝ) / ((2 * k : ℕ) : ℝ)) =
      2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  push_cast
  congr 2
  field_simp


/-- `‖β̂ − β‖₀ ≤ 2k` for `β̂, β ∈ B0(k)`. -/
lemma l0_diff {p : ℕ} (k : ℕ) (βhat β : Fin p → ℝ) (h1 : l0 βhat ≤ k) (h2 : l0 β ≤ k) :
    l0 (βhat - β) ≤ 2 * k := by
  have := l0_sub_le βhat β
  omega

/-- From (29) and (30) and the lower bound on `λ`, derive (31). -/
lemma slow31 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ)
    (σ : ℝ) (k : ℕ) (lam : ℝ) (βhat β : Fin p → ℝ) (hσ : 0 < σ)
    (hlam : (8 + 2 * Real.sqrt 2) * σ *
      Real.sqrt (2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ))) ≤ lam)
    (hbest : IsL2BestSubset X (fun i => fstar i + ε i) k lam βhat) (hβ : β ∈ B0 k)
    (h30 : dot ε (X.mulVec (βhat - β)) ≤
        (4 + Real.sqrt 2) * σ *
          Real.sqrt (2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ))) *
            l2 (β - βhat)) :
    l2 (resid X fstar βhat) ^ 2 ≤ l2 (resid X fstar β) ^ 2 + 2 * lam * l2 β := by
  have h29 := (basic X fstar ε k lam βhat β hbest hβ).2
  set s := Real.sqrt (2 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (k : ℝ))) with hs_def
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hK : 0 ≤ (4 + Real.sqrt 2) * σ * s := by positivity
  have hlam' : 2 * ((4 + Real.sqrt 2) * σ * s) ≤ lam := by linarith
  have hlam0 : 0 ≤ lam := by linarith
  have htri : l2 (β - βhat) ≤ l2 β + l2 βhat := l2_sub_le _ _
  have h1 : 2 * ((4 + Real.sqrt 2) * σ * s) * l2 (β - βhat) ≤ lam * l2 (β - βhat) :=
    mul_le_mul_of_nonneg_right hlam' (l2_nonneg _)
  have h2 : lam * l2 (β - βhat) ≤ lam * (l2 β + l2 βhat) :=
    mul_le_mul_of_nonneg_left htri hlam0
  nlinarith

/-- From (29) and (32), derive (33). -/
lemma slow33 {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ)
    (σ δ0 : ℝ) (k : ℕ) (lam : ℝ) (βhat β : Fin p → ℝ) (hσ : 0 < σ) (hlam0 : 0 ≤ lam)
    (hbest : IsL2BestSubset X (fun i => fstar i + ε i) k lam βhat) (hβ : β ∈ B0 k)
    (h32 : dot ε (X.mulVec (βhat - β)) ≤
        (4 + Real.sqrt 2) * σ * Real.sqrt (Real.log (1 / δ0)) * l2 (X.mulVec (β - βhat))) :
    l2 (resid X fstar βhat) ^ 2 ≤
        l2 (resid X fstar β) ^ 2 + lam * l2 β +
          2 * (4 + Real.sqrt 2) * σ * Real.sqrt (Real.log (1 / δ0)) *
            (l2 (resid X fstar βhat) + l2 (resid X fstar β)) := by
  have h29 := (basic X fstar ε k lam βhat β hbest hβ).2
  have hK : 0 ≤ (4 + Real.sqrt 2) * σ * Real.sqrt (Real.log (1 / δ0)) := by positivity
  have h1 := mul_le_mul_of_nonneg_left (l2_mulVec_le X fstar βhat β) hK
  have h2 : 0 ≤ lam * l2 βhat := mul_nonneg hlam0 (l2_nonneg _)
  nlinarith

/-- `γ_s ‖v‖ ≤ ‖Xv‖` for every `v ∈ B0(s)`. -/
lemma gam_mul_le {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (s : ℕ) (v : Fin p → ℝ)
    (hv : l0 v ≤ s) : gam X s * l2 v ≤ l2 (X.mulVec v) := by
  by_cases hv0 : v = 0
  · subst hv0
    have : l2 (0 : Fin p → ℝ) = 0 := by simp [l2]
    rw [this, mul_zero]
    exact l2_nonneg _
  · have hpos := l2_pos v hv0
    have hle : gam X s ≤ l2 (X.mulVec v) / l2 v := by
      unfold gam
      refine ciInf_le ⟨0, ?_⟩ (⟨v, hv0, hv⟩ : {u : Fin p → ℝ // u ≠ 0 ∧ l0 u ≤ s})
      rintro _ ⟨w, rfl⟩
      exact div_nonneg (l2_nonneg _) (l2_nonneg _)
    rwa [le_div_iff₀ hpos] at hle

end SubsetShrink.L2.Aux

open SubsetShrink.L2

theorem solution {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (fstar ε : Fin n → ℝ)
    (σ δ0 : ℝ) (k : ℕ) (lam : ℝ) (βhat β : Fin p → ℝ)
    (hX : UnitCols X) (hσ : 0 < σ) (hk : 1 ≤ k) (hkp : k ≤ p)
    (hδ0 : 0 < δ0) (hδ1 : δ0 ≤ 1) (hlam : 0 ≤ lam)
    (hG : ε ∈ G X σ δ0 (2 * k))
    (hbest : IsL2BestSubset X (fun i => fstar i + ε i) k lam βhat) (hβ : β ∈ B0 k) :
    l2 (resid X fstar βhat) ^ 2 ≤
      l2 (resid X fstar β) ^ 2 +
        2 * σ * Real.sqrt (10 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (2 * (k : ℝ))) +
          Real.log (1 / δ0)) * (l2 (resid X fstar βhat) + l2 (resid X fstar β)) +
        lam * l2 (β - βhat) := by
  have hu := SubsetShrink.L2.Aux.l0_diff k βhat β hbest.1 hβ
  have hG' := hG (βhat - β) hu
  have hr : (5 * ((2 * k : ℕ) : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / ((2 * k : ℕ) : ℝ)) +
      Real.log (1 / δ0)) =
      10 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (2 * (k : ℝ))) + Real.log (1 / δ0) := by
    push_cast; ring
  rw [hr, SubsetShrink.L2.Aux.l2_mulVec_comm] at hG'
  have h29 := (SubsetShrink.L2.Aux.basic X fstar ε k lam βhat β hbest hβ).2
  have hr0 : 0 ≤ σ * Real.sqrt (10 * (k : ℝ) * Real.log (Real.exp 1 * (p : ℝ) / (2 * (k : ℝ))) +
      Real.log (1 / δ0)) := by positivity
  have h1 := mul_le_mul_of_nonneg_left (SubsetShrink.L2.Aux.l2_mulVec_le X fstar βhat β) hr0
  have h2 := mul_le_mul_of_nonneg_left (SubsetShrink.L2.Aux.l2_le_sub_add β βhat) hlam
  nlinarith
