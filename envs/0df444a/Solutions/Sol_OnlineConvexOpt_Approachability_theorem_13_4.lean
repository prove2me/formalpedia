-- Prove2me | solution 1 for OnlineConvexOpt.Approachability.theorem_13_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T16:26:25.168131+00:00
-- url     : https://prove2.me/submissions/1ba70990-d73b-4349-8b77-8aaa0041cf2f

import Mathlib
import Definitions.Def_OnlineConvexOpt_Approachability_IsBiaffineOn
import Definitions.Def_OnlineConvexOpt_Approachability_IsApproachable
import Definitions.Def_OnlineConvexOpt_Approachability_IsUniformlyApproachable

set_option autoImplicit false

namespace BlackwellAux

open Finset Module

section Affine

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- `f` preserves two-point convex combinations on `K`. -/
def AffOn (K : Set E) (f : E → F) : Prop :=
  ∀ x ∈ K, ∀ y ∈ K, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) = a • f x + b • f y

lemma sum_mul_smul {ι M : Type*} [AddCommGroup M] [Module ℝ M] (s : Finset ι) (k : ℝ)
    (g : ι → ℝ) (V : ι → M) :
    ∑ i ∈ s, (k * g i) • V i = k • ∑ i ∈ s, g i • V i := by
  rw [smul_sum]
  exact sum_congr rfl (fun i _ => mul_smul _ _ _)

lemma sub2 {K : Set E} (hK : Convex ℝ K) {f : E → F} (hf : AffOn K f) {x₀ x y : E}
    (h0 : x₀ ∈ K) (hx : x ∈ K) (hy : y ∈ K) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hs : α + β ≤ 1) :
    x₀ + α • (x - x₀) + β • (y - x₀) ∈ K ∧
    f (x₀ + α • (x - x₀) + β • (y - x₀)) = f x₀ + α • (f x - f x₀) + β • (f y - f x₀) := by
  rcases eq_or_lt_of_le (add_nonneg hα hβ) with h | h
  · have ha : α = 0 := by linarith
    have hb : β = 0 := by linarith
    subst ha; subst hb
    simp [h0]
  · have hne : α + β ≠ 0 := h.ne'
    have hsum : α / (α + β) + β / (α + β) = 1 := by
      rw [← add_div, div_self hne]
    have hm : (α / (α + β)) • x + (β / (α + β)) • y ∈ K :=
      hK hx hy (div_nonneg hα h.le) (div_nonneg hβ h.le) hsum
    have e1 : (α + β) * (α / (α + β)) = α := by field_simp
    have e2 : (α + β) * (β / (α + β)) = β := by field_simp
    have hpt : x₀ + α • (x - x₀) + β • (y - x₀) =
        (1 - (α + β)) • x₀ + (α + β) • ((α / (α + β)) • x + (β / (α + β)) • y) := by
      rw [smul_add, smul_smul, smul_smul, e1, e2]
      simp only [smul_sub, sub_smul, one_smul, add_smul]
      abel
    have hfm := hf x hx y hy (α / (α + β)) (β / (α + β)) (div_nonneg hα h.le)
      (div_nonneg hβ h.le) hsum
    have hfp := hf x₀ h0 _ hm (1 - (α + β)) (α + β) (by linarith) h.le (by ring)
    refine ⟨?_, ?_⟩
    · rw [hpt]
      exact hK h0 hm (by linarith) h.le (by ring)
    · rw [hpt, hfp, hfm, smul_add, smul_smul, smul_smul, e1, e2]
      simp only [smul_sub, sub_smul, one_smul, add_smul]
      abel

lemma subN {K : Set E} (hK : Convex ℝ K) {f : E → F} (hf : AffOn K f) {x₀ : E} (h0 : x₀ ∈ K)
    {ι : Type*} (s : Finset ι) (q : ι → E) :
    (∀ i ∈ s, q i ∈ K) → ∀ w : ι → ℝ, (∀ i ∈ s, 0 ≤ w i) → ∑ i ∈ s, w i ≤ 1 →
    x₀ + ∑ i ∈ s, w i • (q i - x₀) ∈ K ∧
    f (x₀ + ∑ i ∈ s, w i • (q i - x₀)) = f x₀ + ∑ i ∈ s, w i • (f (q i) - f x₀) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro _ w _ _
    simp [h0]
  · intro a s ha ih hq w hw hsum
    have hq' : ∀ i ∈ s, q i ∈ K := fun i hi => hq i (mem_insert_of_mem hi)
    have hqa : q a ∈ K := hq a (mem_insert_self a s)
    have hwa : 0 ≤ w a := hw a (mem_insert_self a s)
    have hws : ∀ i ∈ s, 0 ≤ w i := fun i hi => hw i (mem_insert_of_mem hi)
    rw [sum_insert ha] at hsum
    rw [sum_insert ha, sum_insert ha, ← add_assoc, ← add_assoc]
    obtain ⟨W, hW⟩ : ∃ W, W = ∑ i ∈ s, w i := ⟨_, rfl⟩
    rw [← hW] at hsum
    have hW0 : 0 ≤ W := hW ▸ sum_nonneg hws
    rcases eq_or_lt_of_le hW0 with hz | hpos
    · have hzero : ∀ i ∈ s, w i = 0 :=
        (sum_eq_zero_iff_of_nonneg hws).1 (by rw [← hW, hz])
      have e1 : ∑ i ∈ s, w i • (q i - x₀) = 0 :=
        sum_eq_zero (fun i hi => by rw [hzero i hi, zero_smul])
      have e2 : ∑ i ∈ s, w i • (f (q i) - f x₀) = 0 :=
        sum_eq_zero (fun i hi => by rw [hzero i hi, zero_smul])
      have := sub2 hK hf h0 hqa h0 hwa le_rfl (by linarith)
      rw [e1, e2]
      simpa using this
    · obtain ⟨hzK, hzf⟩ := ih hq' (fun i => W⁻¹ * w i)
        (fun i hi => mul_nonneg (inv_nonneg.2 hW0) (hws i hi))
        (by rw [← mul_sum, ← hW, inv_mul_cancel₀ hpos.ne'])
      simp only [sum_mul_smul] at hzK hzf
      have hz1 : W • (x₀ + W⁻¹ • ∑ i ∈ s, w i • (q i - x₀) - x₀) = ∑ i ∈ s, w i • (q i - x₀) := by
        rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      have hz2 : W • (f (x₀ + W⁻¹ • ∑ i ∈ s, w i • (q i - x₀)) - f x₀) =
          ∑ i ∈ s, w i • (f (q i) - f x₀) := by
        rw [hzf, add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      obtain ⟨h1, h2⟩ := sub2 hK hf h0 hqa hzK hwa hW0 hsum
      rw [hz1] at h1 h2
      rw [hz2] at h2
      exact ⟨h1, h2⟩

lemma signed_ab {K : Set E} (hK : Convex ℝ K) {f : E → F} (hf : AffOn K f) {x₀ x : E}
    (h0 : x₀ ∈ K) (hx : x ∈ K) {ι : Type*} (s : Finset ι) (q : ι → E) (hq : ∀ i ∈ s, q i ∈ K)
    (a b : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) (hb : ∀ i ∈ s, 0 ≤ b i)
    (hrep : x - x₀ = ∑ i ∈ s, a i • (q i - x₀) - ∑ i ∈ s, b i • (q i - x₀)) :
    f x - f x₀ = ∑ i ∈ s, a i • (f (q i) - f x₀) - ∑ i ∈ s, b i • (f (q i) - f x₀) := by
  have hA : 0 ≤ ∑ i ∈ s, a i := sum_nonneg ha
  have hB : 0 ≤ ∑ i ∈ s, b i := sum_nonneg hb
  obtain ⟨N₁, hN₁⟩ : ∃ N : ℝ, N = 1 + ∑ i ∈ s, a i + ∑ i ∈ s, b i := ⟨_, rfl⟩
  have hN₁p : 0 < N₁ := by rw [hN₁]; linarith
  have hNp : 0 < N₁ + 1 := by linarith
  obtain ⟨hPbK, hPbf⟩ := subN hK hf h0 s q hq (fun i => N₁⁻¹ * b i)
    (fun i hi => mul_nonneg (inv_nonneg.2 hN₁p.le) (hb i hi))
    (by rw [← mul_sum, inv_mul_le_iff₀ hN₁p, mul_one]; linarith)
  obtain ⟨_, hPaf⟩ := subN hK hf h0 s q hq (fun i => (N₁ + 1)⁻¹ * a i)
    (fun i hi => mul_nonneg (inv_nonneg.2 hNp.le) (ha i hi))
    (by rw [← mul_sum, inv_mul_le_iff₀ hNp, mul_one]; linarith)
  simp only [sum_mul_smul] at hPbK hPbf hPaf
  have hαβ : (N₁ + 1)⁻¹ + N₁ * (N₁ + 1)⁻¹ ≤ 1 := by
    rw [← one_add_mul, add_comm (1 : ℝ) N₁, mul_inv_cancel₀ hNp.ne']
  obtain ⟨_, hL⟩ := sub2 hK hf h0 hx hPbK (inv_nonneg.2 hNp.le)
    (mul_nonneg hN₁p.le (inv_nonneg.2 hNp.le)) hαβ
  have ec : N₁ * (N₁ + 1)⁻¹ * N₁⁻¹ = (N₁ + 1)⁻¹ := by field_simp
  have hpt : x₀ + (N₁ + 1)⁻¹ • (x - x₀) +
      (N₁ * (N₁ + 1)⁻¹) • (x₀ + N₁⁻¹ • ∑ i ∈ s, b i • (q i - x₀) - x₀) =
      x₀ + (N₁ + 1)⁻¹ • ∑ i ∈ s, a i • (q i - x₀) := by
    rw [hrep, add_sub_cancel_left, smul_smul, ec, smul_sub]
    abel
  rw [hpt, hPaf, hPbf, add_sub_cancel_left, smul_smul, ec, add_assoc] at hL
  have h3 := add_left_cancel hL
  rw [← smul_add] at h3
  have h4 := congrArg (fun z => (N₁ + 1) • z) h3
  simp only [smul_smul, mul_inv_cancel₀ hNp.ne', one_smul] at h4
  rw [eq_sub_iff_add_eq]
  exact h4.symm

lemma signed {K : Set E} (hK : Convex ℝ K) {f : E → F} (hf : AffOn K f) {x₀ x : E}
    (h0 : x₀ ∈ K) (hx : x ∈ K) {ι : Type*} (s : Finset ι) (q : ι → E) (hq : ∀ i ∈ s, q i ∈ K)
    (c : ι → ℝ) (hrep : x - x₀ = ∑ i ∈ s, c i • (q i - x₀)) :
    f x - f x₀ = ∑ i ∈ s, c i • (f (q i) - f x₀) := by
  have hcab : ∀ i, c i = max (c i) 0 - max (-c i) 0 := by
    intro i
    rcases le_total (c i) 0 with h | h
    · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]; ring
    · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]; ring
  have keyF : ∑ i ∈ s, c i • (f (q i) - f x₀) = ∑ i ∈ s, max (c i) 0 • (f (q i) - f x₀) -
      ∑ i ∈ s, max (-c i) 0 • (f (q i) - f x₀) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun i _ => by rw [← sub_smul, ← hcab i])
  have keyE : ∑ i ∈ s, c i • (q i - x₀) = ∑ i ∈ s, max (c i) 0 • (q i - x₀) -
      ∑ i ∈ s, max (-c i) 0 • (q i - x₀) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl (fun i _ => by rw [← sub_smul, ← hcab i])
  rw [keyF]
  refine signed_ab hK hf h0 hx s q hq _ _ (fun i _ => le_max_right _ _)
    (fun i _ => le_max_right _ _) ?_
  rw [← keyE]
  exact hrep

end Affine

section Rep

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

lemma rep (D : Set E) : ∃ s : Finset E, (↑s : Set E) ⊆ D ∧ ∃ c : E → (E →ₗ[ℝ] ℝ),
    ∀ v ∈ D, v = ∑ e ∈ s, c e v • e := by
  classical
  obtain ⟨b, hbD, hspan, hli⟩ := exists_linearIndependent ℝ D
  obtain ⟨s, rfl⟩ := hli.setFinite.exists_finset_coe
  have hext : ∀ i : (↑s : Set E), ∃ g : E →ₗ[ℝ] ℝ,
      g.comp (Submodule.span ℝ (Set.range ((↑) : (↑s : Set E) → E))).subtype =
        (Basis.span hli).coord i :=
    fun i => LinearMap.exists_extend ((Basis.span hli).coord i)
  choose g hg using hext
  refine ⟨s, hbD, fun e => if he : e ∈ s then g ⟨e, he⟩ else 0, ?_⟩
  intro v hv
  have hvW : v ∈ Submodule.span ℝ (Set.range ((↑) : (↑s : Set E) → E)) := by
    rw [Subtype.range_coe, hspan]
    exact Submodule.subset_span hv
  have key : ∀ i : (↑s : Set E), (Basis.span hli).repr ⟨v, hvW⟩ i =
      (if he : (i : E) ∈ s then g ⟨i, he⟩ else 0) v := by
    intro i
    rw [dif_pos (show (i : E) ∈ s from i.2)]
    have := LinearMap.congr_fun (hg i) ⟨v, hvW⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      Basis.coord_apply] at this
    exact this.symm
  calc v = ((⟨v, hvW⟩ : Submodule.span ℝ (Set.range ((↑) : (↑s : Set E) → E))) : E) := rfl
    _ = ((∑ i, (Basis.span hli).repr ⟨v, hvW⟩ i • (Basis.span hli) i :
          Submodule.span ℝ (Set.range ((↑) : (↑s : Set E) → E))) : E) := by
        rw [(Basis.span hli).sum_repr]
    _ = ∑ i : (↑s : Set E), (Basis.span hli).repr ⟨v, hvW⟩ i • (i : E) := by
        rw [Submodule.coe_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Submodule.coe_smul, Basis.coe_span_apply]
    _ = ∑ i : (↑s : Set E), (fun e => (if he : e ∈ s then g ⟨e, he⟩ else 0) v • e) i := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [key i]
    _ = ∑ e ∈ s, (if he : e ∈ s then g ⟨e, he⟩ else 0) v • e := by
        convert Finset.sum_finset_coe (fun e => (if he : e ∈ s then g ⟨e, he⟩ else 0) v • e) s

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

lemma rep_aff {K : Set E} (hK : Convex ℝ K) {x₀ : E} (hx₀ : x₀ ∈ K) :
    ∃ s : Finset E, ∃ c : E → (E →ₗ[ℝ] ℝ), (∀ e ∈ s, x₀ + e ∈ K) ∧
      ∀ f : E → F, AffOn K f → ∀ x ∈ K,
        f x = f x₀ + ∑ e ∈ s, c e (x - x₀) • (f (x₀ + e) - f x₀) := by
  obtain ⟨s, hsD, c, hc⟩ := rep ((fun x => x - x₀) '' K)
  have hq : ∀ e ∈ s, x₀ + e ∈ K := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := hsD he
    simpa using hx
  refine ⟨s, c, hq, fun f hf x hx => ?_⟩
  have hmem : x - x₀ ∈ (fun x => x - x₀) '' K := ⟨x, hx, rfl⟩
  have hr : x - x₀ = ∑ e ∈ s, c e (x - x₀) • ((x₀ + e) - x₀) := by
    simp only [add_sub_cancel_left]
    exact hc _ hmem
  have h := signed hK hf hx₀ hx s (fun e => x₀ + e) hq (fun e => c e (x - x₀)) hr
  rw [← h]
  abel

end Rep

section Cont

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma cont_of_aff {K : Set E} (hK : Convex ℝ K) {f : E → F} (hf : AffOn K f) :
    ContinuousOn f K := by
  rcases K.eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · rw [h]; exact continuousOn_empty f
  obtain ⟨s, c, _, hrep⟩ := rep_aff (F := F) hK hx₀
  have hG : Continuous (fun x => f x₀ + ∑ e ∈ s, c e (x - x₀) • (f (x₀ + e) - f x₀)) := by
    refine continuous_const.add (continuous_finsetSum _ (fun e _ => ?_))
    exact ((c e).continuous_of_finiteDimensional.comp
      (continuous_id.sub continuous_const)).smul continuous_const
  exact hG.continuousOn.congr (fun x hx => hrep f hf x hx)

end Cont

section Seq

variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]

lemma near_le {q p s : D} (h : inner ℝ (q - p) (s - p) ≤ 0) : ‖q - p‖ ≤ ‖q - s‖ := by
  have e : q - s = (q - p) - (s - p) := by abel
  have h2 : ‖q - s‖ ^ 2 = ‖q - p‖ ^ 2 - 2 * inner ℝ (q - p) (s - p) + ‖s - p‖ ^ 2 := by
    rw [e, norm_sub_sq_real]
  by_contra hlt
  push_neg at hlt
  have h3 := mul_self_lt_mul_self (norm_nonneg _) hlt
  rw [pow_two, pow_two, pow_two] at h2
  nlinarith [mul_self_nonneg ‖s - p‖]

lemma nearest {S : Set D} [CompleteSpace D] (hS : IsClosed S) (hSc : Convex ℝ S)
    (hne : S.Nonempty) (q : D) : ∃ p ∈ S, ∀ s ∈ S, inner ℝ (q - p) (s - p) ≤ 0 := by
  obtain ⟨p, hp, hpe⟩ := exists_norm_eq_iInf_of_complete_convex hne hS.isComplete hSc q
  exact ⟨p, hp, (norm_eq_iInf_iff_real_inner_le_zero hSc hp).1 hpe⟩

lemma blackwell_seq (S : Set D) (P : D → D) (hPS : ∀ q, P q ∈ S)
    (hPin : ∀ q, ∀ s ∈ S, inner ℝ (q - P q) (s - P q) ≤ 0) (v : ℕ → D) (M : ℝ)
    (hv : ∀ t : ℕ, ‖v t - P ((t : ℝ)⁻¹ • ∑ s ∈ range t, v s)‖ ≤ M)
    (hcross : ∀ t : ℕ, inner ℝ ((t : ℝ)⁻¹ • ∑ s ∈ range t, v s - P ((t : ℝ)⁻¹ • ∑ s ∈ range t, v s))
      (v t - P ((t : ℝ)⁻¹ • ∑ s ∈ range t, v s)) ≤ 0) :
    ∀ t : ℕ, ‖∑ s ∈ range t, v s - (t : ℝ) • P ((t : ℝ)⁻¹ • ∑ s ∈ range t, v s)‖ ^ 2 ≤
      t * M ^ 2 := by
  intro t
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨z, hz⟩ : ∃ z, z = ∑ s ∈ range t, v s := ⟨_, rfl⟩
    have hvt : ‖v t - P ((t : ℝ)⁻¹ • z)‖ ≤ M := hz ▸ hv t
    have hct : inner ℝ ((t : ℝ)⁻¹ • z - P ((t : ℝ)⁻¹ • z)) (v t - P ((t : ℝ)⁻¹ • z)) ≤ 0 :=
      hz ▸ hcross t
    rw [← hz] at ih
    rw [sum_range_succ, ← hz]
    have hcast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    obtain ⟨p, hp⟩ : ∃ p, p = P ((t : ℝ)⁻¹ • z) := ⟨_, rfl⟩
    rw [← hp] at hvt hct ih
    have htz : (t : ℝ) • ((t : ℝ)⁻¹ • z) = z := by
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · subst h0; simp [hz]
      · rw [smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
    have hT1 : (0 : ℝ) < (t : ℝ) + 1 := by positivity
    have ht1z : ((t : ℝ) + 1) • (((t : ℝ) + 1)⁻¹ • (z + v t)) = z + v t := by
      rw [smul_smul, mul_inv_cancel₀ hT1.ne', one_smul]
    have hnear : ‖((t : ℝ) + 1)⁻¹ • (z + v t) - P (((t : ℝ) + 1)⁻¹ • (z + v t))‖ ≤
        ‖((t : ℝ) + 1)⁻¹ • (z + v t) - p‖ := near_le (hPin _ p (hp ▸ hPS _))
    have e1 : ∀ r : D, z + v t - ((t : ℝ) + 1) • r =
        ((t : ℝ) + 1) • (((t : ℝ) + 1)⁻¹ • (z + v t) - r) := by
      intro r; rw [smul_sub, ht1z]
    have h1 : ‖z + v t - ((t : ℝ) + 1) • P (((t : ℝ) + 1)⁻¹ • (z + v t))‖ ≤
        ‖z + v t - ((t : ℝ) + 1) • p‖ := by
      rw [e1, e1, norm_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left hnear (norm_nonneg _)
    have e2 : z + v t - ((t : ℝ) + 1) • p = (z - (t : ℝ) • p) + (v t - p) := by
      rw [add_smul, one_smul]; abel
    have e3 : z - (t : ℝ) • p = (t : ℝ) • ((t : ℝ)⁻¹ • z - p) := by rw [smul_sub, htz]
    have hc : inner ℝ (z - (t : ℝ) • p) (v t - p) ≤ 0 := by
      rw [e3, real_inner_smul_left]
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg t) hct
    have hvt2 : ‖v t - p‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hvt 2
    have h2 : ‖z + v t - ((t : ℝ) + 1) • p‖ ^ 2 ≤ t * M ^ 2 + M ^ 2 := by
      rw [e2, norm_add_sq_real]
      linarith
    calc _ ≤ ‖z + v t - ((t : ℝ) + 1) • p‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ t * M ^ 2 + M ^ 2 := h2
      _ = ((t : ℝ) + 1) * M ^ 2 := by ring

end Seq

section Alg

variable {X Y D : Type*} [AddCommGroup D] [Module ℝ D]

noncomputable def cumS (u : X → Y → D) (orc : D → X) : (t : ℕ) → (Fin t → Y) → D
  | 0, _ => 0
  | t + 1, h => cumS u orc t (Fin.init h) +
      u (orc (((t : ℝ))⁻¹ • cumS u orc t (Fin.init h))) (h (Fin.last t))

noncomputable def alg (u : X → Y → D) (orc : D → X) (t : ℕ) (h : Fin t → Y) : X :=
  orc ((t : ℝ)⁻¹ • cumS u orc t h)

lemma cumS_eq (u : X → Y → D) (orc : D → X) (y : ℕ → Y) : ∀ t : ℕ,
    cumS u orc t (fun i : Fin t => y i) =
      ∑ s ∈ Finset.range t, u (alg u orc s (fun i : Fin s => y i)) (y s)
  | 0 => by simp [cumS]
  | t + 1 => by
      rw [Finset.sum_range_succ, ← cumS_eq u orc y t]
      rfl

end Alg

open OnlineConvexOpt.Approachability

lemma bound_u {n m d : ℕ} {K₁ : Set (EuclideanSpace ℝ (Fin n))}
    {K₂ : Set (EuclideanSpace ℝ (Fin m))}
    {u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d)}
    (hK₁k : IsCompact K₁) (hK₂k : IsCompact K₂) (hK₁c : Convex ℝ K₁) (hK₂c : Convex ℝ K₂)
    (hu : IsBiaffineOn K₁ K₂ u) : ∃ B, ∀ x ∈ K₁, ∀ y ∈ K₂, ‖u x y‖ ≤ B := by
  rcases K₁.eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · exact ⟨0, by simp [h]⟩
  have hcy : ∀ x ∈ K₁, ContinuousOn (u x) K₂ := fun x hx => cont_of_aff hK₂c (hu.2 x hx)
  obtain ⟨s, c, hs, hrep⟩ := rep_aff (F := EuclideanSpace ℝ (Fin d)) hK₁c hx₀
  have hG : ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) =>
      u x₀ p.2 + ∑ e ∈ s, c e (p.1 - x₀) • (u (x₀ + e) p.2 - u x₀ p.2)) (K₁ ×ˢ K₂) := by
    apply ContinuousOn.add
    · exact (hcy x₀ hx₀).comp continuousOn_snd (fun p hp => hp.2)
    · apply continuousOn_finsetSum
      intro e he
      have h1 : ContinuousOn (fun a : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) =>
          c e (a.1 - x₀)) (K₁ ×ˢ K₂) :=
        ((c e).continuous_of_finiteDimensional.comp
          (continuous_fst.sub continuous_const)).continuousOn
      have h2 : ContinuousOn (fun a : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) =>
          u (x₀ + e) a.2 - u x₀ a.2) (K₁ ×ˢ K₂) :=
        ((hcy _ (hs e he)).comp continuousOn_snd (fun p hp => hp.2)).sub
          ((hcy x₀ hx₀).comp continuousOn_snd (fun p hp => hp.2))
      exact h1.smul h2
  obtain ⟨C, hC⟩ := (hK₁k.prod hK₂k).exists_bound_of_continuousOn hG
  refine ⟨C, fun x hx y hy => ?_⟩
  have h := hrep (fun x => u x y) (hu.1 y hy) x hx
  try simp only at h
  rw [h]
  exact hC (x, y) ⟨hx, hy⟩

theorem suff {n m d : ℕ} (K₁ : Set (EuclideanSpace ℝ (Fin n)))
    (K₂ : Set (EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hK₁k : IsCompact K₁) (hK₁c : Convex ℝ K₁) (hK₁ne : K₁.Nonempty)
    (hK₂k : IsCompact K₂) (hK₂c : Convex ℝ K₂)
    (hS : IsClosed S) (hSb : Bornology.IsBounded S) (hSc : Convex ℝ S) (hSne : S.Nonempty)
    (hu : IsBiaffineOn K₁ K₂ u) :
    (∀ y ∈ K₂, ∃ x ∈ K₁, u x y ∈ S) → IsUniformlyApproachable K₁ K₂ u S := by
  intro hcond
  obtain ⟨x₀, hx₀⟩ := hK₁ne
  have hcx : ∀ y ∈ K₂, ContinuousOn (fun x => u x y) K₁ :=
    fun y hy => cont_of_aff hK₁c (hu.1 y hy)
  have hcy : ∀ x ∈ K₁, ContinuousOn (u x) K₂ := fun x hx => cont_of_aff hK₂c (hu.2 x hx)
  choose P hPS hPin using nearest hS hSc hSne
  have hex : ∀ q, ∃ x ∈ K₁, ∀ y ∈ K₂, inner ℝ (q - P q) (u x y - P q) ≤ 0 := by
    intro q
    rcases K₂.eq_empty_or_nonempty with h | hK₂ne
    · exact ⟨x₀, hx₀, by simp [h]⟩
    obtain ⟨a, ha, b, hb, hsad⟩ := Sion.exists_isSaddlePointOn
      (f := fun x y => inner ℝ (q - P q) (u x y))
      ⟨x₀, hx₀⟩ hK₁c hK₁k
      (fun y hy => (continuousOn_const.inner (hcx y hy)).lowerSemicontinuousOn)
      (fun y hy => ConvexOn.quasiconvexOn ⟨hK₁c, fun x hx x' hx' α β hα hβ hαβ => le_of_eq (by
        simp only [hu.1 y hy x hx x' hx' α β hα hβ hαβ, inner_add_right, real_inner_smul_right,
          smul_eq_mul])⟩)
      hK₂c hK₂ne hK₂k
      (fun x hx => (continuousOn_const.inner (hcy x hx)).upperSemicontinuousOn)
      (fun x hx => ConcaveOn.quasiconcaveOn ⟨hK₂c, fun y hy y' hy' α β hα hβ hαβ => le_of_eq (by
        simp only [hu.2 x hx y hy y' hy' α β hα hβ hαβ, inner_add_right, real_inner_smul_right,
          smul_eq_mul])⟩)
    obtain ⟨xb, hxb, hxbS⟩ := hcond b hb
    refine ⟨a, ha, fun y hy => ?_⟩
    have h1 : inner ℝ (q - P q) (u a y) ≤ inner ℝ (q - P q) (u xb b) := hsad xb hxb y hy
    have h2 := hPin q _ hxbS
    rw [inner_sub_right] at h2 ⊢
    linarith
  choose orc horcK horc using hex
  obtain ⟨Bu, hBu⟩ := bound_u hK₁k hK₂k hK₁c hK₂c hu
  obtain ⟨Bs, hBs⟩ := hSb.exists_norm_le
  refine ⟨alg u orc, fun t h _ => horcK _, fun ε hε => ?_⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = Bu + Bs := ⟨_, rfl⟩
  refine ⟨Nat.ceil (M ^ 2 / ε ^ 2) + 1, fun T hT y hy => ?_⟩
  have hAt : ∀ t, alg u orc t (fun i : Fin t => y i) = orc ((t : ℝ)⁻¹ •
      ∑ s ∈ Finset.range t, u (alg u orc s (fun i : Fin s => y i)) (y s)) := fun t => by
    show orc ((t : ℝ)⁻¹ • cumS u orc t (fun i : Fin t => y i)) = _
    rw [cumS_eq]
  have hinv := blackwell_seq S P hPS hPin
    (fun t => u (alg u orc t (fun i : Fin t => y i)) (y t)) M
    (fun t => by
      rw [hAt t, hM]
      calc _ ≤ ‖u (orc _) (y t)‖ + ‖P _‖ := norm_sub_le _ _
        _ ≤ Bu + Bs := add_le_add (hBu _ (horcK _) _ (hy t)) (hBs _ (hPS _)))
    (fun t => by
      rw [hAt t]
      exact horc _ _ (hy t))
    T
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast le_trans (Nat.le_add_left 1 _) hT
  have hTpos : (0 : ℝ) < T := by linarith
  obtain ⟨z, hz⟩ : ∃ z, z = ∑ s ∈ Finset.range T, u (alg u orc s (fun i : Fin s => y i)) (y s) :=
    ⟨_, rfl⟩
  have havg : avgPayoff u (alg u orc) y T = (T : ℝ)⁻¹ • z := by rw [hz]; rfl
  rw [havg]
  rw [← hz] at hinv
  obtain ⟨p, hp⟩ : ∃ p, p = P ((T : ℝ)⁻¹ • z) := ⟨_, rfl⟩
  rw [← hp] at hinv
  have hd : Metric.infDist ((T : ℝ)⁻¹ • z) S ≤ ‖(T : ℝ)⁻¹ • z - p‖ := by
    rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem (hp ▸ hPS _)
  have hTz : z - (T : ℝ) • p = (T : ℝ) • ((T : ℝ)⁻¹ • z - p) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hTpos.ne', one_smul]
  rw [hTz, norm_smul, Real.norm_eq_abs, abs_of_pos hTpos, mul_pow] at hinv
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ‖(T : ℝ)⁻¹ • z - p‖ := ⟨_, rfl⟩
  rw [← hδ] at hinv hd
  have hceil : M ^ 2 / ε ^ 2 ≤ (T : ℝ) := by
    have h1 := Nat.le_ceil (M ^ 2 / ε ^ 2)
    have h2 : ((Nat.ceil (M ^ 2 / ε ^ 2) + 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast hT
    push_cast at h2
    linarith
  have hM2 : M ^ 2 ≤ T * ε ^ 2 := by
    rwa [div_le_iff₀ (by positivity)] at hceil
  have hTd : T * δ ^ 2 ≤ M ^ 2 := by
    have : (T : ℝ) * (T * δ ^ 2) ≤ T * M ^ 2 := by
      calc (T : ℝ) * (T * δ ^ 2) = T ^ 2 * δ ^ 2 := by ring
        _ ≤ _ := hinv
    exact le_of_mul_le_mul_left this hTpos
  refine le_trans hd ?_
  by_contra hlt
  push_neg at hlt
  have h1 : ε * ε < δ * δ := mul_self_lt_mul_self hε.le hlt
  have h2 : (T : ℝ) * (ε * ε) < T * (δ * δ) := mul_lt_mul_of_pos_left h1 hTpos
  rw [← pow_two, ← pow_two] at h2
  linarith

theorem necc {n m d : ℕ} (K₁ : Set (EuclideanSpace ℝ (Fin n)))
    (K₂ : Set (EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hK₁k : IsCompact K₁) (hK₁c : Convex ℝ K₁)
    (hS : IsClosed S) (hSne : S.Nonempty) (hu : IsBiaffineOn K₁ K₂ u) :
    IsApproachable K₁ K₂ u S → ∀ y ∈ K₂, ∃ x ∈ K₁, u x y ∈ S := by
  intro happ y₀ hy₀
  by_contra hno
  push_neg at hno
  obtain ⟨A, hA, hlim⟩ := happ
  have hcx : ContinuousOn (fun x => u x y₀) K₁ := cont_of_aff hK₁c (hu.1 y₀ hy₀)
  have hg : ContinuousOn (fun x => Metric.infDist (u x y₀) S) K₁ :=
    (Metric.continuous_infDist_pt S).comp_continuousOn hcx
  have hA0 : A 0 (fun _ => y₀) ∈ K₁ := hA 0 _ (fun _ => hy₀)
  obtain ⟨xm, hxm, hmin⟩ := hK₁k.exists_isMinOn ⟨_, hA0⟩ hg
  have hpos : 0 < Metric.infDist (u xm y₀) S := by
    rcases (Metric.infDist_nonneg (x := u xm y₀) (s := S)).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hno xm hxm
      rw [← hS.closure_eq, Metric.mem_closure_iff_infDist_zero hSne]
      exact h.symm
  have hev := (hlim (fun _ => y₀) (fun _ => hy₀)).eventually (gt_mem_nhds hpos)
  obtain ⟨T, hT, hT1⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT1
  obtain ⟨hbarK, hbarf⟩ := subN hK₁c (f := fun x => u x y₀) (hu.1 y₀ hy₀) hxm (Finset.range T)
    (fun t => A t (fun _ => y₀)) (fun t _ => hA t _ (fun _ => hy₀)) (fun _ => (T : ℝ)⁻¹)
    (fun _ _ => inv_nonneg.2 hTpos.le)
    (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_inv_cancel₀ hTpos.ne'])
  try simp only at hbarf
  have hid : u xm y₀ + ∑ t ∈ Finset.range T, (T : ℝ)⁻¹ • (u (A t (fun _ => y₀)) y₀ - u xm y₀) =
      (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, u (A t (fun _ => y₀)) y₀ := by
    rw [← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, smul_sub,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hTpos.ne', one_smul]
    abel
  have havg : avgPayoff u A (fun _ => y₀) T =
      u (xm + ∑ t ∈ Finset.range T, (T : ℝ)⁻¹ • (A t (fun _ => y₀) - xm)) y₀ := by
    rw [hbarf, hid]; rfl
  have h4 : Metric.infDist (u xm y₀) S ≤
      Metric.infDist (u (xm + ∑ t ∈ Finset.range T, (T : ℝ)⁻¹ • (A t (fun _ => y₀) - xm)) y₀) S :=
    isMinOn_iff.mp hmin _ hbarK
  have hT' : Metric.infDist (avgPayoff u A (fun _ => y₀) T) S < Metric.infDist (u xm y₀) S := hT
  rw [havg] at hT'
  linarith

theorem unif_app {n m d : ℕ} (K₁ : Set (EuclideanSpace ℝ (Fin n)))
    (K₂ : Set (EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d))) :
    IsUniformlyApproachable K₁ K₂ u S → IsApproachable K₁ K₂ u S := by
  intro h
  obtain ⟨A, hA, hU⟩ := h
  refine ⟨A, hA, fun y hy => ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := hU (ε / 2) (half_pos hε)
  refine ⟨T₀, fun T hT => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.infDist_nonneg]
  linarith [hT₀ T hT y hy]

end BlackwellAux

open OnlineConvexOpt.Approachability in
theorem solution {n m d : ℕ} (K₁ : Set (EuclideanSpace ℝ (Fin n)))
    (K₂ : Set (EuclideanSpace ℝ (Fin m)))
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d))
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (hK₁ : IsClosed K₁) (hK₁b : Bornology.IsBounded K₁) (hK₁c : Convex ℝ K₁)
    (hK₁ne : K₁.Nonempty)
    (hK₂ : IsClosed K₂) (hK₂b : Bornology.IsBounded K₂) (hK₂c : Convex ℝ K₂)
    (hS : IsClosed S) (hSb : Bornology.IsBounded S) (hSc : Convex ℝ S) (hSne : S.Nonempty)
    (hu : IsBiaffineOn K₁ K₂ u) :
    ((∀ y ∈ K₂, ∃ x ∈ K₁, u x y ∈ S) ↔ IsApproachable K₁ K₂ u S) ∧
      ((∀ y ∈ K₂, ∃ x ∈ K₁, u x y ∈ S) ↔ IsUniformlyApproachable K₁ K₂ u S) := by
  have hK₁k : IsCompact K₁ := Metric.isCompact_of_isClosed_isBounded hK₁ hK₁b
  have hK₂k : IsCompact K₂ := Metric.isCompact_of_isClosed_isBounded hK₂ hK₂b
  have h1 := BlackwellAux.suff K₁ K₂ u S hK₁k hK₁c hK₁ne hK₂k hK₂c hS hSb hSc hSne hu
  have h3 := BlackwellAux.necc K₁ K₂ u S hK₁k hK₁c hS hSne hu
  have h2 := BlackwellAux.unif_app K₁ K₂ u S
  exact ⟨⟨fun h => h2 (h1 h), h3⟩, ⟨h1, fun h => h3 (h2 h)⟩⟩
