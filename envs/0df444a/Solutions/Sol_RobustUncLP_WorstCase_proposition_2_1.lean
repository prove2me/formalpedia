-- Prove2me | solution 1 for RobustUncLP.WorstCase.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T15:08:53.625662+00:00
-- url     : https://prove2.me/submissions/c4cdab91-57ec-45de-9c71-754515e376af

import Mathlib
import Definitions.Def_RobustUncLP_WorstCase_Setting

set_option autoImplicit false

namespace RobustP21

open Matrix RobustUncLP.WorstCase

lemma exists_between_fin {ι : Type} (s r : Finset ι) (L U : ι → ℝ)
    (h : ∀ q ∈ s, ∀ p ∈ r, L q ≤ U p) :
    ∃ t : ℝ, (∀ q ∈ s, L q ≤ t) ∧ ∀ p ∈ r, t ≤ U p := by
  by_cases hs : s.Nonempty
  · refine ⟨s.sup' hs L, fun q hq => Finset.le_sup' L hq, fun p hp => ?_⟩
    exact Finset.sup'_le hs L (fun q hq => h q hq p hp)
  · by_cases hr : r.Nonempty
    · exact ⟨r.inf' hr U, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => Finset.inf'_le U hp⟩
    · exact ⟨0, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => absurd ⟨p, hp⟩ hr⟩

/-- Theorem of alternatives (Fourier–Motzkin), variables indexed by `Fin n`. -/
theorem fm_alt (n : ℕ) : ∀ {ι : Type} [Fintype ι] (a : ι → Fin n → ℝ) (b : ι → ℝ),
    (∃ x : Fin n → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℝ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  induction n with
  | zero =>
    intro ι _ a b
    classical
    by_cases h : ∀ i, 0 ≤ b i
    · left; exact ⟨0, fun i => by simpa using h i⟩
    · right
      push Not at h
      obtain ⟨i, hi⟩ := h
      refine ⟨fun j => if j = i then 1 else 0, fun j => ?_, fun s => s.elim0, ?_⟩
      · dsimp only; split_ifs <;> norm_num
      · simpa using hi
  | succ n ih =>
    intro ι _ a b
    classical
    let W : ι ⊕ (ι × ι) → ι → ℝ := Sum.elim (fun z i => if a z 0 = 0 ∧ i = z then 1 else 0)
      (fun pq i => if 0 < a pq.1 0 ∧ a pq.2 0 < 0 then
        (if i = pq.1 then -a pq.2 0 else 0) + (if i = pq.2 then a pq.1 0 else 0) else 0)
    have hW0 : ∀ k i, 0 ≤ W k i := by
      intro k i
      rcases k with z | ⟨p, q⟩
      · simp only [W, Sum.elim_inl]; split_ifs <;> norm_num
      · simp only [W, Sum.elim_inr]
        split_ifs with h1 h2 h3 h3 <;> subst_vars <;> first | linarith [h1.1, h1.2] | norm_num
    let C : ι ⊕ (ι × ι) → Fin (n + 1) → ℝ := fun k s => ∑ i, W k i * a i s
    let D : ι ⊕ (ι × ι) → ℝ := fun k => ∑ i, W k i * b i
    have hC0 : ∀ k, C k 0 = 0 := by
      intro k
      rcases k with z | ⟨p, q⟩
      · by_cases hz : a z 0 = 0
        · simp [C, W, hz]
        · simp [C, W, hz]
      · by_cases h : 0 < a p 0 ∧ a q 0 < 0
        · simp only [C, W, Sum.elim_inr, if_pos h, add_mul, ite_mul, zero_mul,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        · simp [C, W, h]
    rcases ih (fun k s => C k s.succ) D with ⟨y, hy⟩ | ⟨μ, hμ0, hμ1, hμ2⟩
    · left
      let r : ι → ℝ := fun i => b i - ∑ s : Fin n, a i s.succ * y s
      have key : ∀ k, 0 ≤ ∑ i, W k i * r i := by
        intro k
        have e : ∑ i, W k i * r i = D k - ∑ s, C k s.succ * y s := by
          simp only [r, D, C, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
            mul_assoc]
          congr 1
          exact Finset.sum_comm
        rw [e]; linarith [hy k]
      have kinl : ∀ z, a z 0 = 0 → 0 ≤ r z := by
        intro z hz
        have := key (Sum.inl z)
        simpa [W, hz] using this
      have kinr : ∀ p q, 0 < a p 0 → a q 0 < 0 → 0 ≤ -a q 0 * r p + a p 0 * r q := by
        intro p q hp hq
        have := key (Sum.inr (p, q))
        simp only [W, Sum.elim_inr, if_pos (And.intro hp hq), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
        exact this
      obtain ⟨t, ht1, ht2⟩ := exists_between_fin (Finset.univ.filter (fun q => a q 0 < 0))
        (Finset.univ.filter (fun p => 0 < a p 0)) (fun q => r q / a q 0) (fun p => r p / a p 0)
        (by
          intro q hq p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hp
          have h := kinr p q hp hq
          have e : -a q 0 * r p + a p 0 * r q =
              -(a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0)) := by
            have h1 : r p = (r p / a p 0) * a p 0 := (div_mul_cancel₀ _ hp.ne').symm
            have h2 : r q = (r q / a q 0) * a q 0 := (div_mul_cancel₀ _ hq.ne).symm
            set U := r p / a p 0
            set V := r q / a q 0
            rw [h1, h2]; ring
          by_contra hc
          push Not at hc
          have hpq : 0 < a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0) :=
            mul_pos (mul_pos hp (neg_pos.2 hq)) (sub_pos.2 hc)
          linarith)
      refine ⟨Fin.cons t y, fun i => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hr : r i = b i - ∑ s : Fin n, a i s.succ * y s := rfl
      suffices a i 0 * t ≤ r i by linarith
      rcases lt_trichotomy (a i 0) 0 with hneg | hz | hpos
      · have := ht1 i (by simp [hneg])
        rw [div_le_iff_of_neg hneg] at this
        linarith
      · rw [hz, zero_mul]; exact kinl i hz
      · have := ht2 i (by simp [hpos])
        rw [le_div_iff₀ hpos] at this
        linarith
    · right
      refine ⟨fun i => ∑ k, μ k * W k i, fun i => Finset.sum_nonneg
        (fun k _ => mul_nonneg (hμ0 k) (hW0 k i)), fun s => ?_, ?_⟩
      · have e : ∑ i, (∑ k, μ k * W k i) * a i s = ∑ k, μ k * C k s := by
          simp only [C, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]
        refine Fin.cases ?_ (fun s => ?_) s
        · simp [hC0]
        · exact hμ1 s
      · have e : ∑ i, (∑ k, μ k * W k i) * b i = ∑ k, μ k * D k := by
          simp only [D, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]; exact hμ2



lemma isClosed_instFeas {m n : ℕ} (f : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) :
    IsClosed (instFeas f A) := by
  have h1 : IsClosed {x : Fin n → ℝ | 0 ≤ A *ᵥ x} :=
    isClosed_le continuous_const (Continuous.matrix_mulVec continuous_const continuous_id)
  have h2 : IsClosed {x : Fin n → ℝ | f ⬝ᵥ x = 1} :=
    isClosed_eq (Continuous.dotProduct continuous_const continuous_id) continuous_const
  exact h1.inter h2

lemma convex_rowProj {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) (hconv : Convex ℝ U)
    (i : Fin m) : Convex ℝ (rowProj U i) := by
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩ s t hs ht hst
  exact ⟨s • A + t • B, hconv hA hB hs ht hst, by ext j; simp⟩

lemma key {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) (f g : Fin n → ℝ)
    (hconv : Convex ℝ U) (hcw : IsConstraintWise U) (A0 : Matrix (Fin m) (Fin n) ℝ)
    (hA0 : A0 ∈ U) (hK : IsCompact (instFeas f A0))
    (hemp : ∀ x : Fin n → ℝ, (∀ A ∈ U, 0 ≤ A *ᵥ x) → 0 ≤ g ⬝ᵥ x → f ⬝ᵥ x ≠ 1) :
    ∃ A ∈ U, ∀ x : Fin n → ℝ, 0 ≤ A *ᵥ x → 0 ≤ g ⬝ᵥ x → f ⬝ᵥ x ≠ 1 := by
  classical
  have hK' : IsCompact (instFeas f A0 ∩ {x | 0 ≤ g ⬝ᵥ x}) :=
    hK.inter_right (isClosed_le continuous_const
      (Continuous.dotProduct continuous_const continuous_id))
  obtain ⟨u, hu⟩ := hK'.elim_finite_subfamily_closed
    (fun A : U => {x : Fin n → ℝ | 0 ≤ (A : Matrix (Fin m) (Fin n) ℝ) *ᵥ x})
    (fun A => isClosed_le continuous_const
      (Continuous.matrix_mulVec continuous_const continuous_id)) (by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro x ⟨⟨⟨_, hfx⟩, hg⟩, hall⟩
      rw [Set.mem_iInter] at hall
      exact hemp x (fun A hA => hall ⟨A, hA⟩) hg hfx)
  rw [Set.eq_empty_iff_forall_notMem] at hu
  let B : Option u → Matrix (Fin m) (Fin n) ℝ :=
    fun o => o.elim A0 (fun a => ((a : U) : Matrix (Fin m) (Fin n) ℝ))
  have hBU : ∀ o, B o ∈ U := by
    intro o
    cases o with
    | none => exact hA0
    | some a => exact (a : U).2
  let a : (Fin 2 ⊕ (Option u × Fin m)) → Fin n → ℝ :=
    Sum.elim ![-f, -g] (fun p => -(B p.1 p.2))
  let b : (Fin 2 ⊕ (Option u × Fin m)) → ℝ :=
    Sum.elim ![-1, 0] (fun _ => 0)
  rcases fm_alt n a b with ⟨x, hx⟩ | ⟨l, hl0, hl1, hl2⟩
  · exfalso
    have hf : 1 ≤ f ⬝ᵥ x := by
      have := hx (Sum.inl 0)
      simp only [a, b, Sum.elim_inl, Matrix.cons_val_zero, Pi.neg_apply, neg_mul,
        Finset.sum_neg_distrib] at this
      simp only [dotProduct]; linarith
    have hg : 0 ≤ g ⬝ᵥ x := by
      have := hx (Sum.inl 1)
      simp only [a, b, Sum.elim_inl, Matrix.cons_val_one, Matrix.cons_val_zero,
        Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
      simp only [dotProduct]; linarith
    have hB : ∀ o, 0 ≤ B o *ᵥ x := by
      intro o i
      have := hx (Sum.inr (o, i))
      simp only [a, b, Sum.elim_inr, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at this
      simp only [Pi.zero_apply, Matrix.mulVec, dotProduct]; linarith
    have hfpos : 0 < f ⬝ᵥ x := by linarith
    set r := (f ⬝ᵥ x)⁻¹ with hr
    have hr0 : 0 < r := inv_pos.2 hfpos
    apply hu (r • x)
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [Matrix.mulVec_smul]; exact smul_nonneg hr0.le (hB none)
    · rw [dotProduct_smul, smul_eq_mul, hr, inv_mul_cancel₀ hfpos.ne']
    · show 0 ≤ g ⬝ᵥ (r • x)
      rw [dotProduct_smul, smul_eq_mul]; exact mul_nonneg hr0.le hg
    · rw [Set.mem_iInter₂]
      intro A hA
      show 0 ≤ (A : Matrix (Fin m) (Fin n) ℝ) *ᵥ (r • x)
      rw [Matrix.mulVec_smul]; exact smul_nonneg hr0.le (hB (some ⟨A, hA⟩))
  · have hl2' : 0 < l (Sum.inl 0) := by
      simp only [b, Fintype.sum_sum_type, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mul_zero,
        Finset.sum_const_zero, add_zero, mul_neg, mul_one] at hl2
      linarith
    let S : Fin m → ℝ := fun i => ∑ o, l (Sum.inr (o, i))
    have hS0 : ∀ i, 0 ≤ S i := fun i => Finset.sum_nonneg (fun o _ => hl0 _)
    let w : Fin m → Option u → ℝ := fun i o =>
      if S i = 0 then (if o = none then 1 else 0) else l (Sum.inr (o, i)) / S i
    let A : Matrix (Fin m) (Fin n) ℝ := Matrix.of fun i => ∑ o, w i o • B o i
    have hAU : A ∈ U := by
      apply hcw
      intro i
      show ∑ o, w i o • B o i ∈ rowProj U i
      apply (convex_rowProj U hconv i).sum_mem
      · intro o _
        simp only [w]
        split_ifs
        · norm_num
        · norm_num
        · exact div_nonneg (hl0 _) (hS0 i)
      · simp only [w]
        split_ifs with h
        · simp
        · rw [← Finset.sum_div]; exact div_self h
      · intro o _
        exact ⟨B o, hBU o, rfl⟩
    refine ⟨A, hAU, ?_⟩
    intro x hAx hgx hfx
    have e1 : ∑ k, l k * (a k ⬝ᵥ x) = 0 := by
      have : ∑ k, l k * (a k ⬝ᵥ x) = ∑ s, (∑ k, l k * a k s) * x s := by
        simp only [dotProduct, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
      rw [this]; simp [hl1]
    have hrow : ∀ i, ∑ o, l (Sum.inr (o, i)) * (B o i ⬝ᵥ x) = S i * (A *ᵥ x) i := by
      intro i
      have hAi : (A *ᵥ x) i = ∑ o, w i o * (B o i ⬝ᵥ x) := by
        simp only [A, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
      by_cases h : S i = 0
      · have hz : ∀ o, l (Sum.inr (o, i)) = 0 := by
          intro o
          exact (Finset.sum_eq_zero_iff_of_nonneg (fun o _ => hl0 _)).1 h o (Finset.mem_univ _)
        simp [hz, h]
      · rw [hAi, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun o _ => ?_)
        simp only [w, if_neg h]
        field_simp
    have hT : 0 ≤ ∑ o, ∑ i, l (Sum.inr (o, i)) * (B o i ⬝ᵥ x) := by
      rw [Finset.sum_comm]
      refine Finset.sum_nonneg (fun i _ => ?_)
      rw [hrow i]
      exact mul_nonneg (hS0 i) (hAx i)
    simp only [a, Fintype.sum_sum_type, Fin.sum_univ_two, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, neg_dotProduct,
      Fintype.sum_prod_type, mul_neg, Finset.sum_neg_distrib] at e1
    rw [hfx] at e1
    have := mul_nonneg (hl0 (Sum.inl 1)) hgx
    linarith

lemma part_i {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ)) (f : Fin n → ℝ)
    (hconv : Convex ℝ U) (hne : U.Nonempty) (hcw : IsConstraintWise U)
    (hbdd : BoundednessAssumption U f) :
    robustFeas U f = ∅ ↔ ∃ A ∈ U, instFeas f A = ∅ := by
  constructor
  · intro h
    obtain ⟨A0, hA0⟩ := hne
    obtain ⟨Q, -, hQ, hsub⟩ := hbdd
    have hK : IsCompact (instFeas f A0) :=
      hQ.of_isClosed_subset (isClosed_instFeas f A0) (hsub A0 hA0)
    obtain ⟨A, hA, hno⟩ := key U f 0 hconv hcw A0 hA0 hK (by
      intro x hx _ hfx
      have hx' : x ∈ robustFeas U f := ⟨hx, hfx⟩
      rw [h] at hx'; exact hx')
    exact ⟨A, hA, Set.eq_empty_iff_forall_notMem.2 fun x hx => hno x hx.1 (by simp) hx.2⟩
  · rintro ⟨A, hA, hemp⟩
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    have hx' : x ∈ instFeas f A := ⟨hx.1 A hA, hx.2⟩
    rw [hemp] at hx'; exact hx'

end RobustP21

open Matrix RobustUncLP.WorstCase in
theorem solution {m n : ℕ} (U : Set (Matrix (Fin m) (Fin n) ℝ))
    (c f : Fin n → ℝ)
    (hconv : Convex ℝ U) (hclosed : IsClosed U) (hne : U.Nonempty)
    (hcw : IsConstraintWise U) (hbdd : BoundednessAssumption U f) :
    (robustFeas U f = ∅ ↔ ∃ A ∈ U, instFeas f A = ∅) ∧
    ∀ cstar : ℝ, (robustFeas U f).Nonempty →
      IsGLB ((fun x => c ⬝ᵥ x) '' robustFeas U f) cstar →
      IsLUB {v : ℝ | ∃ A ∈ U, IsGLB ((fun x => c ⬝ᵥ x) '' instFeas f A) v} cstar := by
  refine ⟨RobustP21.part_i U f hconv hne hcw hbdd, fun cstar hGne hglb => ⟨?_, ?_⟩⟩
  · rintro v ⟨A, hA, hv⟩
    apply hglb.2
    rintro _ ⟨x, hx, rfl⟩
    exact hv.1 ⟨x, ⟨hx.1 A hA, hx.2⟩, rfl⟩
  · intro w hw
    by_contra hlt
    push Not at hlt
    obtain ⟨A0, hA0⟩ := hne
    obtain ⟨Q, -, hQ, hsub⟩ := hbdd
    have hK : ∀ A ∈ U, IsCompact (instFeas f A) := fun A hA =>
      hQ.of_isClosed_subset (RobustP21.isClosed_instFeas f A) (hsub A hA)
    have hdot : ∀ x : Fin n → ℝ,
        (((w + cstar) / 2) • f - c) ⬝ᵥ x = (w + cstar) / 2 * (f ⬝ᵥ x) - c ⬝ᵥ x := by
      intro x; rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    obtain ⟨A, hA, hno⟩ := RobustP21.key U f (((w + cstar) / 2) • f - c) hconv hcw A0 hA0
      (hK A0 hA0) (by
        intro x hx hg hfx
        have hxG : x ∈ robustFeas U f := ⟨hx, hfx⟩
        have h1 : cstar ≤ c ⬝ᵥ x := hglb.1 ⟨x, hxG, rfl⟩
        rw [hdot, hfx] at hg
        linarith)
    obtain ⟨x1, hx1⟩ := hGne
    have hne' : (instFeas f A).Nonempty := ⟨x1, hx1.1 A hA, hx1.2⟩
    obtain ⟨x0, hx0, hmin⟩ := (hK A hA).exists_isMinOn hne'
      (Continuous.dotProduct continuous_const continuous_id).continuousOn
    have hglbA : IsGLB ((fun x => c ⬝ᵥ x) '' instFeas f A) (c ⬝ᵥ x0) := by
      refine IsLeast.isGLB ⟨⟨x0, hx0, rfl⟩, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact hmin hy
    have hv : c ⬝ᵥ x0 ≤ w := hw ⟨A, hA, hglbA⟩
    apply hno x0 hx0.1 _ hx0.2
    rw [hdot, hx0.2]
    linarith
