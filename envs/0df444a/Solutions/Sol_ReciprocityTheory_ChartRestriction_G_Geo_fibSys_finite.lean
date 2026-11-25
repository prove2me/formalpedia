-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.fibSys_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:05:27.289656+00:00
-- url     : https://prove2.me/submissions/f096a1c4-1305-4b25-8365-974730217183

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFibA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {W : Type*} [Fintype W] (r : W → ℕ) (H : W → MvPolynomial W ℂ)
    (hH : ∀ i, (H i).totalDegree < r i) :
    {w : W → ℂ | ∀ i, w i ^ r i = eval w (H i)}.Finite := by
  classical
  rcases isEmpty_or_nonempty W with hW | hW
  · exact Set.Subsingleton.finite fun x _ y _ => funext fun i => (IsEmpty.false i).elim
  obtain ⟨B, hB⟩ : ∃ B : Finset (W →₀ ℕ), ∀ u, u ∈ B ↔ ∀ i, u i < r i := by
    refine ⟨(Fintype.piFinset fun i => Finset.range (r i)).map
      Finsupp.equivFunOnFinite.symm.toEmbedding, fun u => ?_⟩
    rw [Finset.mem_map_equiv, Equiv.symm_symm, Fintype.mem_piFinset]
    simp [Finset.mem_range]
  obtain ⟨M, hMdef⟩ : ∃ M : Submodule ℂ (MvPolynomial W ℂ),
      M = Submodule.span ℂ ((fun b => monomial b (1 : ℂ)) '' (B : Set (W →₀ ℕ))) := ⟨_, rfl⟩
  have hmon : ∀ (n : ℕ) (u : W →₀ ℕ), u.degree ≤ n → ∀ a : ℂ, ∃ q ∈ M,
      ∀ w : W → ℂ, (∀ i, w i ^ r i = eval w (H i)) → eval w (monomial u a) = eval w q := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro u hu a
    by_cases hall : ∀ i, u i < r i
    · refine ⟨monomial u a, ?_, fun _ _ => rfl⟩
      have e : monomial u a = a • monomial u (1 : ℂ) := by rw [smul_monomial, smul_eq_mul, mul_one]
      rw [e, hMdef]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨u, (hB u).mpr hall, rfl⟩)
    · push_neg at hall
      obtain ⟨i, hi⟩ := hall
      have hle : Finsupp.single i (r i) ≤ u := Finsupp.single_le_iff.mpr hi
      obtain ⟨u', hu'⟩ : ∃ u', u = u' + Finsupp.single i (r i) :=
        ⟨u - Finsupp.single i (r i), (tsub_add_cancel_of_le hle).symm⟩
      have hdeg : u'.degree + r i = u.degree := by
        rw [hu', map_add, Finsupp.degree_single]
      have hsplit : ∀ w : W → ℂ, (∀ i, w i ^ r i = eval w (H i)) →
          eval w (monomial u a) = eval w (monomial u' a * H i) := by
        intro w hw
        rw [hu', show monomial (u' + Finsupp.single i (r i)) a =
          monomial u' a * monomial (Finsupp.single i (r i)) 1 by rw [monomial_mul, mul_one],
          map_mul, map_mul, ← X_pow_eq_monomial, map_pow, eval_X, hw i]
      have hsum : monomial u' a * H i =
          ∑ v ∈ (H i).support, monomial (u' + v) (a * coeff v (H i)) := by
        conv_lhs => rw [(H i).as_sum]
        rw [Finset.mul_sum]
        simp only [monomial_mul]
      have hterm : ∀ v ∈ (H i).support, ∃ q ∈ M, ∀ w : W → ℂ, (∀ i, w i ^ r i = eval w (H i)) →
          eval w (monomial (u' + v) (a * coeff v (H i))) = eval w q := by
        intro v hv
        have hv' : v.degree ≤ (H i).totalDegree := le_totalDegree hv
        have hlt : (u' + v).degree < n := by
          rw [map_add]
          have := hH i
          omega
        exact ih _ hlt _ le_rfl _
      choose q hqM hq using hterm
      refine ⟨∑ v ∈ (H i).support.attach, q v.1 v.2, Submodule.sum_mem _ fun v _ => hqM v.1 v.2, ?_⟩
      intro w hw
      rw [hsplit w hw, hsum, map_sum, map_sum]
      exact (Finset.sum_attach _ _).symm.trans (Finset.sum_congr rfl fun v _ => hq v.1 v.2 w hw)
  have hA : ∀ p : MvPolynomial W ℂ, ∃ q ∈ M, ∀ w : W → ℂ, (∀ i, w i ^ r i = eval w (H i)) →
      eval w p = eval w q := by
    intro p
    refine MvPolynomial.induction_on' p (fun u a => hmon _ u le_rfl a) (fun p q hp hq => ?_)
    obtain ⟨p', hp'M, hp'⟩ := hp
    obtain ⟨q', hq'M, hq'⟩ := hq
    exact ⟨p' + q', M.add_mem hp'M hq'M, fun w hw => by rw [map_add, map_add, hp' w hw, hq' w hw]⟩
  have hex : ∀ x y : W → ℂ, ∃ i, x ≠ y → x i ≠ y i := fun x y => by
    by_cases h : x = y
    · exact ⟨Classical.arbitrary W, fun h' => (h' h).elim⟩
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
      exact ⟨i, fun _ => hi⟩
  choose idx hidx using hex
  by_contra hinf
  have hinf' : Set.Infinite {w : W → ℂ | ∀ i, w i ^ r i = eval w (H i)} := hinf
  obtain ⟨T, hTS, hTcard⟩ := hinf'.exists_subset_card_eq (B.card + 1)
  let Φ : (B → ℂ) →ₗ[ℂ] (T → ℂ) :=
    { toFun := fun c t => ∑ b : B, c b * eval (t : W → ℂ) (monomial (b : W →₀ ℕ) 1)
      map_add' := fun c c' => by
        funext t
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun a c => by
        funext t
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hΦ : ∀ c t, Φ c t = ∑ b : B, c b * eval (t : W → ℂ) (monomial (b : W →₀ ℕ) 1) :=
    fun _ _ => rfl
  have key : ∀ q ∈ M, ∃ c : B → ℂ, ∀ t : T, eval (t : W → ℂ) q = Φ c t := by
    intro q hq
    rw [hMdef] at hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      refine ⟨Pi.single ⟨b, hb⟩ 1, fun t => ?_⟩
      rw [hΦ, Finset.sum_eq_single ⟨b, hb⟩]
      · simp
      · intro b' _ hb'
        simp [Pi.single_apply, hb']
      · simp
    | zero => exact ⟨0, fun t => by simp [hΦ]⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc⟩ := hx
      obtain ⟨c', hc'⟩ := hy
      exact ⟨c + c', fun t => by rw [map_add, hc, hc', map_add]; rfl⟩
    | smul a x _ hx =>
      obtain ⟨c, hc⟩ := hx
      exact ⟨a • c, fun t => by rw [MvPolynomial.smul_eval, hc, map_smul]; rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : (W → ℂ) → MvPolynomial W ℂ, ∀ x, L x = ∏ y ∈ T.erase x,
      (C ((x (idx x y) - y (idx x y))⁻¹) * (X (idx x y) - C (y (idx x y)))) := ⟨_, fun _ => rfl⟩
  have hLself : ∀ x, eval x (L x) = 1 := by
    intro x
    rw [hL, map_prod]
    refine Finset.prod_eq_one fun y hy => ?_
    have hne : x ≠ y := (Finset.ne_of_mem_erase hy).symm
    rw [map_mul, eval_C, map_sub, eval_X, eval_C, inv_mul_cancel₀ (sub_ne_zero.mpr (hidx x y hne))]
  have hLother : ∀ x, ∀ z ∈ T, z ≠ x → eval z (L x) = 0 := by
    intro x z hz hzx
    rw [hL, map_prod]
    refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hzx, hz⟩) ?_
    rw [map_mul, map_sub, eval_X, eval_C, eval_C, sub_self, mul_zero]
  have hsurj : Function.Surjective Φ := by
    intro f
    obtain ⟨f', hf'⟩ : ∃ f' : (W → ℂ) → ℂ, ∀ t : T, f' t = f t :=
      ⟨fun x => if h : x ∈ T then f ⟨x, h⟩ else 0, fun t => by simp [t.2]⟩
    obtain ⟨q, hqM, hq⟩ := hA (∑ x ∈ T, C (f' x) * L x)
    obtain ⟨c, hc⟩ := key q hqM
    refine ⟨c, funext fun t => ?_⟩
    rw [← hc t, ← hq t (hTS t.2), map_sum, Finset.sum_eq_single (t : W → ℂ)]
    · rw [map_mul, eval_C, hLself, mul_one, hf']
    · intro x _ hxt
      rw [map_mul, hLother x t t.2 (Ne.symm hxt), mul_zero]
    · intro h
      exact absurd t.2 h
  have h1 := LinearMap.finrank_range_le Φ
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_coe] at h1
  omega
end ReciprocityTheory.ChartRestriction.G.Geo
