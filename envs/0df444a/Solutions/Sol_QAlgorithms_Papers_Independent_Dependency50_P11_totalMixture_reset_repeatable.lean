-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P11.totalMixture_reset_repeatable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:57:11.892432+00:00
-- url     : https://prove2.me/submissions/4d901e6a-5d00-46ab-bcdd-aa4109cacf4a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

open scoped Matrix ComplexOrder

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P11 in
open QAlgorithms.Papers.Independent.Information100.P23 (Operator) in
theorem g53h_RU_repeatable {d : ℕ} (E : Superop (Fin d) (Fin d)) (hRU : IsRandomUnitary E) :
    HasFiniteRepeatableImplementation E := by
  classical
  obtain ⟨k, p, V, hp, hsum, hEV⟩ := hRU
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hsum
    · exact h
  let Um : Matrix (Fin k × Fin d) (Fin k × Fin d) ℂ :=
    Matrix.of fun x y => if x.1 = y.1 then (V x.1 : Operator d) x.2 y.2 else 0
  have hVu : ∀ a, star (V a : Operator d) * (V a : Operator d) = 1 :=
    fun a => Matrix.mem_unitaryGroup_iff'.1 (V a).2
  have hUm : Um ∈ Matrix.unitaryGroup (Fin k × Fin d) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff']
    ext ⟨a, i⟩ ⟨b, j⟩
    have e := congrFun (congrFun (hVu a) i) j
    simp only [Matrix.mul_apply, Matrix.star_apply, Fintype.sum_prod_type, Um, Matrix.of_apply] at e ⊢
    by_cases hab : a = b
    · subst hab
      rw [Finset.sum_eq_single a (fun c _ hc => by simp [hc]) (by simp)]
      simp only [↓reduceIte]
      rw [e]
      simp [Matrix.one_apply, Prod.ext_iff]
    · rw [Finset.sum_eq_zero]
      · simp [Matrix.one_apply, Prod.ext_iff, hab]
      · intro c _
        apply Finset.sum_eq_zero; intro l _
        by_cases h1 : c = a
        · subst h1; simp [hab]
        · simp [h1]
  let xi : Operator k := Matrix.diagonal (fun a => (p a : ℂ))
  have hxi : IsDensityMatrix xi := by
    refine ⟨?_, ?_⟩
    · rw [Matrix.posSemidef_diagonal_iff]; intro a; exact_mod_cast (hp a).1
    · simp [xi, Matrix.trace_diagonal]; exact_mod_cast hsum
  let D : MemoryDevice d k := ⟨hk, ⟨Um, hUm⟩, xi, hxi⟩
  have hjoint : ∀ rho : Operator d, jointStep D xi rho =
      fun x y => if x.1 = y.1 then (p x.1 : ℂ) * ((V x.1 : Operator d) * rho * (V x.1 : Operator d)ᴴ) x.2 y.2
        else 0 := by
    intro rho
    ext ⟨a, i⟩ ⟨b, j⟩
    simp only [jointStep, D, Matrix.mul_apply, Fintype.sum_prod_type, Um, Matrix.of_apply, xi, Matrix.kronecker,
      Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, star_zero]
    have inner : ∀ x x1, (∑ x_2, ∑ x_3, if x_2 = x then if a = x_2 then (V a : Operator d) i x_3 *
        ((p x_2 : ℂ) * rho x_3 x1) else 0 else 0) =
        if a = x then (p a : ℂ) * ∑ x_3, (V a : Operator d) i x_3 * rho x_3 x1 else 0 := by
      intro x x1
      rw [Finset.sum_eq_single x (fun c _ hc => by simp [hc]) (by simp)]
      by_cases h : a = x
      · subst h; simp [Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _; ring
      · simp [h]
    simp only [inner]
    by_cases hab : a = b
    · subst hab
      rw [Finset.sum_eq_single a (fun c _ hc => by simp [Ne.symm hc]) (by simp)]
      simp only [↓reduceIte, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      simp; ring
    · rw [if_neg hab]
      apply Finset.sum_eq_zero; intro x _
      apply Finset.sum_eq_zero; intro x1 _
      by_cases h : a = x
      · subst h; simp [Ne.symm hab]
      · simp [h]
  have htr : ∀ (a : Fin k) (rho : Operator d),
      ((V a : Operator d) * rho * (V a : Operator d)ᴴ).trace = rho.trace := by
    intro a rho
    rw [Matrix.trace_mul_cycle, ← Matrix.star_eq_conjTranspose, hVu a, one_mul]
  have hR : ∀ rho : Operator d, IsDensityMatrix rho → traceRight (jointStep D xi rho) = xi := by
    intro rho hrho
    ext a b
    simp only [traceRight, hjoint, Matrix.of_apply]
    by_cases hab : a = b
    · subst hab
      simp only [↓reduceIte]
      rw [← Finset.mul_sum]
      have := htr a rho
      have h2 := hrho.2
      simp only [Matrix.trace, Matrix.diag] at this h2
      rw [this, h2]
      simp [xi]
    · simp [hab, xi]
  have hL : ∀ rho : Operator d, traceLeft (jointStep D xi rho) = E rho := by
    intro rho
    ext i j
    simp only [traceLeft, hjoint, Matrix.of_apply, ↓reduceIte, hEV, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul]
  have hmem : ∀ input : ℕ → Operator d, (∀ j, IsDensityMatrix (input j)) →
      ∀ n, memoryState D input n = xi := by
    intro input hin n
    induction n with
    | zero => rfl
    | succ n ih =>
      show traceRight (jointStep D (memoryState D input n) (input n)) = xi
      rw [ih, hR _ (hin n)]
  refine ⟨k, D, fun n input hin j _ => ?_⟩
  unfold outputState
  rw [hmem input hin j, hL]

open scoped ComplexConjugate Matrix in
theorem g53h_weyl_twirl (d : ℕ) [NeZero d] (X : Matrix (Fin d) (Fin d) ℂ) :
    let e := ZMod.finEquiv d
    let ψ : AddChar (ZMod d) ℂ := ZMod.stdAddChar
    let W : ZMod d → ZMod d → Matrix (Fin d) (Fin d) ℂ := fun a b =>
      Matrix.of fun i j => if e i = e j + a then ψ (b * e j) else 0
    (∀ a b, star (W a b) * W a b = 1) ∧
    ∀ i j, ∑ a, ∑ b, (W a b * X * (W a b)ᴴ) i j = if i = j then (d : ℂ) * X.trace else 0 := by
  intro e ψ W
  have hconj : ∀ x y : ZMod d, ψ x * conj (ψ y) = ψ (x - y) := by
    intro x y; rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, sub_eq_add_neg]
  have hcond : ∀ (i k : Fin d) (a : ZMod d), e i = e k + a ↔ k = e.symm (e i - a) := by
    intro i k a; constructor
    · intro h; apply e.injective; simp [h]
    · intro h; subst h; simp
  refine ⟨fun a b => ?_, fun i j => ?_⟩
  · ext j l
    simp only [Matrix.mul_apply, Matrix.star_apply, W, Matrix.of_apply]
    by_cases hjl : j = l
    · subst hjl
      rw [Finset.sum_eq_single (e.symm (e j + a))]
      · simp only [RingEquiv.apply_symm_apply, if_true, Matrix.one_apply_eq]
        rw [mul_comm, ← starRingEnd_apply, hconj, sub_self, AddChar.map_zero_eq_one]
      · intro c _ hc
        have : ¬ e c = e j + a := fun h => hc (by apply e.injective; simp [h])
        simp [this]
      · simp
    · rw [Matrix.one_apply_ne hjl]
      apply Finset.sum_eq_zero; intro c _
      by_cases h1 : e c = e j + a
      · have : ¬ e c = e l + a := by
          intro h2; apply hjl; apply e.injective; rw [h1] at h2; exact add_right_cancel h2
        simp [this]
      · simp [h1]
  · have hrow : ∀ (a b : ZMod d) (l : Fin d), (W a b * X) i l =
        ψ (b * (e i - a)) * X (e.symm (e i - a)) l := by
      intro a b l
      rw [Matrix.mul_apply, Finset.sum_eq_single (e.symm (e i - a))]
      · simp [W]
      · intro c _ hc
        have : ¬ e i = e c + a := fun h => hc ((hcond i c a).1 h)
        simp [W, this]
      · simp
    have hent : ∀ a b : ZMod d, (W a b * X * (W a b)ᴴ) i j =
        ψ (b * (e i - e j)) * X (e.symm (e i - a)) (e.symm (e j - a)) := by
      intro a b
      rw [Matrix.mul_apply]
      simp only [hrow, Matrix.conjTranspose_apply]
      rw [Finset.sum_eq_single (e.symm (e j - a))]
      · simp only [W, Matrix.of_apply, RingEquiv.apply_symm_apply, sub_add_cancel, if_true]
        rw [mul_right_comm, ← starRingEnd_apply, hconj]
        congr 2; ring
      · intro c _ hc
        have : ¬ e j = e c + a := fun h => hc ((hcond j c a).1 h)
        simp [W, this]
      · simp
    simp only [hent]
    simp only [← Finset.sum_mul]
    have hs := fun c : ZMod d => AddChar.sum_mulShift (ψ := ψ) c (ZMod.isPrimitive_stdAddChar d)
    simp only [hs, ZMod.card]
    by_cases hij : i = j
    · subst hij
      simp only [sub_self, if_true]
      rw [Matrix.trace, ← Finset.mul_sum]
      congr 1
      exact Fintype.sum_equiv ((Equiv.subLeft (e i)).trans e.symm.toEquiv) _ _ (fun a => rfl)
    · have : e i - e j ≠ 0 := fun h => hij (e.injective (sub_eq_zero.1 h))
      simp [this, hij]

noncomputable def g53h_W (d : ℕ) [NeZero d] (a b : ZMod d) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun i j => if ZMod.finEquiv d i = ZMod.finEquiv d j + a then
    (ZMod.stdAddChar : AddChar (ZMod d) ℂ) (b * ZMod.finEquiv d j) else 0

open scoped Matrix in
theorem g53h_weyl2 (d : ℕ) [NeZero d] (X : Matrix (Fin d) (Fin d) ℂ) :
    (∀ a b, star (g53h_W d a b) * g53h_W d a b = 1) ∧
    ∀ i j, ∑ a, ∑ b, (g53h_W d a b * X * (g53h_W d a b)ᴴ) i j =
      if i = j then (d : ℂ) * X.trace else 0 :=
  g53h_weyl_twirl d X

open scoped Matrix in
open QAlgorithms in
theorem g53h_depol_RU (d : ℕ) (hd : 0 < d) :
    QAlgorithms.Papers.Independent.Dependency50.P11.IsRandomUnitary (QuditFidelity.depolarizingMap d hd 1) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  let σ := (Fintype.equivFin (ZMod d × ZMod d)).symm
  have hU := (g53h_weyl2 d 0).1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨Fintype.card (ZMod d × ZMod d), fun _ => 1 / (d : ℝ) ^ 2,
    fun j => ⟨g53h_W d (σ j).1 (σ j).2, Matrix.mem_unitaryGroup_iff'.2 (hU _ _)⟩, ?_, ?_, ?_⟩
  · intro j; refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  · simp [ZMod.card]; field_simp
  · intro X
    ext i j
    have htw := (g53h_weyl2 d X).2 i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    rw [Equiv.sum_comp σ (fun x => (g53h_W d x.1 x.2 * X * (g53h_W d x.1 x.2)ᴴ) i j),
      Fintype.sum_prod_type, htw]
    simp only [QuditFidelity.depolarizingMap, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    split_ifs <;> push_cast <;> field_simp <;> ring

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

/-- Section IV, PDF p.4: the completely mixing reset is random unitary and repeatable.
The accepted depolarizing map at p=1 is its trace-weighted linear extension to operators. -/
theorem solution (d : ℕ) (hd : 0 < d) :
    IsRandomUnitary (QuditFidelity.depolarizingMap d hd 1) ∧
      HasFiniteRepeatableImplementation (QuditFidelity.depolarizingMap d hd 1) := by
  exact ⟨g53h_depol_RU d hd, g53h_RU_repeatable _ (g53h_depol_RU d hd)⟩



end

