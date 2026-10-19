-- Prove2me | solution 1 for QAlgorithms.DeWolf.parityMatchings_qrac
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T03:03:57.625391+00:00
-- url     : https://prove2.me/submissions/0516b56e-0f9a-4235-8e13-7ccf97e26569

import Definitions.Def_QAlgorithms_Defs_Information

set_option autoImplicit false
set_option linter.unusedSimpArgs false
open QAlgorithms
open scoped BigOperators ComplexConjugate ComplexOrder

namespace ParityQRAC

private def rank {β : Type*} (u v : β → ℂ) : Matrix β β ℂ :=
  Matrix.vecMulVec u (star v)

private lemma rank_pos {β : Type*} [Fintype β] (u : β → ℂ) : (rank u u).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star u

private lemma rank_prob {β : Type*} [Fintype β] (u v ψ : β → ℂ) :
    effectProb (rank u v) (rank ψ ψ) =
      ((∑ b, conj (v b) * ψ b) * conj (∑ b, conj (u b) * ψ b)).re := by
  simp only [effectProb, rank, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Complex.star_def, map_sum, map_mul,
    starRingEnd_self_apply, Finset.sum_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma prob_add {β : Type*} [Fintype β]
    (A B ρ : Matrix β β ℂ) : effectProb (A+B) ρ = effectProb A ρ + effectProb B ρ := by
  simp [effectProb, Matrix.add_mul, Matrix.trace_add]

private lemma prob_smul {β : Type*} [Fintype β]
    (c : ℝ) (A ρ : Matrix β β ℂ) : effectProb (c • A) ρ = c * effectProb A ρ := by
  simp [effectProb, Matrix.smul_mul, Matrix.trace_smul, Complex.real_smul]

private lemma prob_sum {β E : Type*} [Fintype β] [Fintype E]
    (A : E → Matrix β β ℂ) (ρ : Matrix β β ℂ) :
    effectProb (∑ e, A e) ρ = ∑ e, effectProb (A e) ρ := by
  simp [effectProb, Matrix.sum_mul, Matrix.trace_sum]

private lemma match_effect {β E : Type*} [Fintype β] [DecidableEq β]
    [Fintype E] [DecidableEq E] (p : E × Bool → β) (hp : Function.Injective p)
    (z : E → ℝ) (hz : ∀ e, z e ^ 2 = 1) :
    ∃ M : Matrix β β ℂ, IsEffect M ∧ ∀ ψ : β → ℂ,
      effectProb M (rank ψ ψ) = (rank ψ ψ).trace.re / 2 +
        ∑ e, z e * (ψ (p (e,false)) * conj (ψ (p (e,true)))).re := by
  classical
  let k : β → β → ℂ := fun b => Pi.single b 1
  let P : Matrix β β ℂ := ∑ eb : E × Bool, rank (k (p eb)) (k (p eb))
  have hP : P = Matrix.diagonal (fun b => if b ∈ Set.range p then 1 else 0) := by
    ext b c
    simp only [P, rank, Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]
    by_cases hbc : b = c
    · subst c
      by_cases h : b ∈ Set.range p
      · obtain ⟨a, rfl⟩ := h
        have hra : p a ∈ Set.range p := ⟨a,rfl⟩
        simp only [Matrix.diagonal_apply_eq, if_pos hra]
        rw [Finset.sum_eq_single a]
        · simp [k]
        · intro b _ hba
          have hpb : p b ≠ p a := fun h => hba (hp h)
          simp [k, Pi.single_apply, hpb]
        · simp
      · have hn : ∀ a, p a ≠ b := fun a ha => h ⟨a,ha⟩
        simp [k, Pi.single_apply, hn, Matrix.diagonal_apply, h]
    · have hz0 : ∀ a : E × Bool, k (p a) b * star (k (p a) c) = 0 := by
        intro a
        by_cases hab : p a = b
        · subst b
          simp [k, Pi.single_apply, hbc]
        · simp [k, Pi.single_apply, hab]
      simp only [Matrix.diagonal_apply_ne _ hbc]
      exact Finset.sum_eq_zero fun a _ => hz0 a
  let D : Matrix β β ℂ := 1-P
  have hD : D.PosSemidef := by
    rw [show D = Matrix.diagonal (fun b => if b ∈ Set.range p then 0 else 1) by
      ext b c
      simp only [D, hP, Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]
      split_ifs <;> simp_all]
    exact Matrix.PosSemidef.diagonal (fun b => by dsimp; split_ifs <;> norm_num)
  let v : (E → ℝ) → E → β → ℂ := fun s e =>
    k (p (e,false)) + (s e : ℂ) • k (p (e,true))
  let S : (E → ℝ) → Matrix β β ℂ := fun s => ∑ e, rank (v s e) (v s e)
  have hS (s : E → ℝ) : (S s).PosSemidef := Matrix.posSemidef_sum _ fun e _ => rank_pos _
  let T : (E → ℝ) → Matrix β β ℂ := fun s => ∑ e, (s e : ℂ) •
    (rank (k (p (e,false))) (k (p (e,true))) +
      rank (k (p (e,true))) (k (p (e,false))))
  have hST (s : E → ℝ) (hs : ∀ e, s e ^ 2 = 1) : S s = P + T s := by
    have hPs : P = ∑ e, (rank (k (p (e,false))) (k (p (e,false))) +
        rank (k (p (e,true))) (k (p (e,true)))) := by
      simp only [P, Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [Finset.sum_add_distrib, add_comm]
    rw [hPs]
    ext b c
    simp only [S, T, Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    have he : (s e : ℂ)^2 = 1 := by exact_mod_cast hs e
    simp only [v, rank, Matrix.vecMulVec_apply, Pi.add_apply, Pi.smul_apply,
      Pi.star_apply, smul_eq_mul, star_add, star_mul, Complex.star_def, Complex.conj_ofReal]
    linear_combination (k (p (e,true)) b * conj (k (p (e,true)) c)) * he
  have hTneg : T (-z) = -T z := by
    simp only [T, Pi.neg_apply, Complex.ofReal_neg, neg_smul]
    rw [Finset.sum_neg_distrib]
  have hsz := hST z hz
  have hsn := hST (-z) (by intro e; simpa using hz e)
  rw [hTneg] at hsn
  let M := (1/2 : ℝ) • (S z + D)
  have hM : M = (1/2 : ℝ) • (1 : Matrix β β ℂ) + (1/2 : ℝ) • T z := by
    dsimp [M, D]
    rw [hsz]
    module
  have hcomp : 1-M = (1/2 : ℝ) • (S (-z) + D) := by
    rw [hM, hsn]
    dsimp [D]
    module
  refine ⟨M, ⟨(hS z |>.add hD).smul (by norm_num : (0:ℝ) ≤ 1/2), ?_⟩, ?_⟩
  · rw [hcomp]
    exact (hS (-z) |>.add hD).smul (by norm_num : (0:ℝ) ≤ 1/2)
  · intro ψ
    rw [hM, prob_add, prob_smul, prob_smul]
    dsimp only [T]
    rw [prob_sum]
    have hone : effectProb (1 : Matrix β β ℂ) (rank ψ ψ) = (rank ψ ψ).trace.re := by
      simp [effectProb]
    rw [hone]
    rw [show (1/2:ℝ) * (rank ψ ψ).trace.re = (rank ψ ψ).trace.re / 2 by ring]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    have hlin (A : Matrix β β ℂ) :
        effectProb ((z e : ℂ) • A) (rank ψ ψ) = z e * effectProb A (rank ψ ψ) := by
      simp [effectProb, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re]
    rw [hlin, prob_add, rank_prob, rank_prob]
    simp [k, Pi.single_apply, Complex.mul_re, mul_comm]
    ring

private def sgn (b : Bool) : ℝ := if b then -1 else 1

private lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> norm_num [sgn]

private noncomputable def phase {α β : Type*} (g : α → β) (y : α → Bool) : β → ℂ :=
  Function.extend g (fun a => (sgn (y a) : ℂ)) 0

private lemma phase_apply {α β : Type*} (g : α → β) (hg : Function.Injective g)
    (y : α → Bool) (a : α) : phase g y (g a) = (sgn (y a) : ℂ) :=
  hg.extend_apply _ _ a

private lemma phase_trace {α β : Type*} [Fintype α] [Fintype β]
    (g : α → β) (hg : Function.Injective g) (y : α → Bool) :
    (rank (phase g y) (phase g y)).trace = Fintype.card α := by
  classical
  change (∑ b, phase g y b * conj (phase g y b)) = _
  have h := Fintype.sum_of_injective g hg (fun _ => (1:ℂ))
    (fun b => phase g y b * conj (phase g y b)) ?_ ?_
  · simpa using h.symm
  · intro b hb
    rw [phase, Function.extend_apply' _ _ _ hb]
    simp
  · intro a
    rw [phase_apply g hg]
    cases h : y a <;> norm_num [sgn, h]

private lemma phase_density {α β : Type*} [Fintype α] [Fintype β] [Nonempty α]
    (g : α → β) (hg : Function.Injective g) (y : α → Bool) :
    IsDensityMatrix ((Fintype.card α : ℝ)⁻¹ • rank (phase g y) (phase g y)) := by
  refine ⟨(rank_pos _).smul (by positivity), ?_⟩
  rw [Matrix.trace_smul, phase_trace g hg]
  have h : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card α ≠ 0)
  simp [Complex.real_smul, h]

private lemma prob_rsmul {β : Type*} [Fintype β]
    (c : ℝ) (A ρ : Matrix β β ℂ) : effectProb A (c • ρ) = c * effectProb A ρ := by
  simp [effectProb, Matrix.mul_smul, Matrix.trace_smul, Complex.real_smul]

private lemma qubit_budget {N : ℕ} (hN : 1 ≤ N) :
    (Nat.clog 2 (2*N) : ℝ) ≤ Real.logb 2 (N:ℝ) + 2 := by
  rw [← Real.natCeil_logb_natCast]
  norm_num only [Nat.cast_ofNat]
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlog : 0 ≤ Real.logb 2 ((2*N:ℕ):ℝ) :=
    Real.logb_nonneg (by norm_num) (by push_cast; linarith)
  have hc := Nat.ceil_lt_add_one hlog
  have hlog2 : Real.logb 2 ((2*N:ℕ):ℝ) = 1 + Real.logb 2 (N:ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.logb_mul (by norm_num) (by positivity),
      Real.logb_self_eq_one (by norm_num)]
  rw [hlog2] at hc ⊢
  linarith


private lemma balanced {n : ℕ} (i : Fin n) (b : Bool) :
    ((Finset.univ.filter fun x : Fin n → Bool => x i = b).card : ℝ) /
      (2:ℝ)^n = 1/2 := by
  classical
  let R := {j : Fin n // j ≠ i} → Bool
  have hsum : (∑ x : Fin n → Bool, if x i = b then (1:ℝ) else 0) = Fintype.card R := by
    rw [← (Equiv.funSplitAt i Bool).symm.sum_comp]
    simp only [Equiv.funSplitAt, Equiv.piSplitAt, Equiv.coe_fn_mk, dif_pos rfl]
    rw [Fintype.sum_prod_type]
    cases b <;> simp [R]
  have hc : (2:ℝ)^n = 2 * Fintype.card R := by
    have h := Fintype.card_congr (Equiv.funSplitAt i Bool)
    simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Fintype.card_prod] at h
    dsimp [R]
    simp only [Fintype.card_fun, Fintype.card_bool]
    exact_mod_cast h
  have hcount : ((Finset.univ.filter fun x : Fin n → Bool => x i = b).card : ℝ) =
      Fintype.card R := by
    simpa only [← Finset.sum_boole, Finset.sum_ite_irrel] using hsum
  rw [hcount]
  have hpos : (0:ℝ) < 2^n := by positivity
  rw [div_eq_iff hpos.ne']
  linarith

private lemma pair_rep {N : ℕ} (t : Finset (Fin N)) (ht : t.Nonempty) (hsize : t.card ≤ 2) :
    ∃ u v : Bool × Fin N, u ≠ v ∧ u.2 ∈ t ∧ v.2 ∈ t ∧
      ∀ y : Fin N → Bool, xor (u.1 && y u.2) (v.1 && y v.2) =
        decide (Odd (t.filter fun j => y j = true).card) := by
  classical
  by_cases h1 : t.card = 1
  · obtain ⟨j,rfl⟩ := Finset.card_eq_one.mp h1
    refine ⟨(true,j),(false,j),by simp,by simp,by simp,?_⟩
    intro y
    cases h : y j <;> simp [Finset.filter_singleton, h]
  · have h2 : t.card = 2 := by have := Finset.card_pos.mpr ht; omega
    obtain ⟨j,k,hjk,rfl⟩ := Finset.card_eq_two.mp h2
    refine ⟨(true,j),(true,k),?_,by simp,by simp,?_⟩
    · simpa using hjk
    · intro y
      cases hj : y j <;> cases hk : y k <;> simp [Finset.filter_insert, Finset.filter_singleton, hj, hk, hjk]

private lemma correlated_nonempty {n N : ℕ} (i : Fin n)
    (C : (Fin n → Bool) → (Fin N → Bool)) (κ : ℝ) (hκ : 0 < κ)
    (t : Finset (Fin N)) (a : Bool)
    (h : 1/2 + κ ≤ ((Finset.univ.filter fun x : Fin n → Bool =>
      x i = xor a (decide (Odd (t.filter fun j => C x j = true).card))).card : ℝ) /
        (2:ℝ)^n) : t.Nonempty := by
  classical
  by_contra ht
  have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
  have hb := balanced i a
  have h' : 1/2 + κ ≤ ((Finset.univ.filter fun x : Fin n → Bool => x i = a).card : ℝ) /
      (2:ℝ)^n := by simpa [he] using h
  rw [hb] at h'
  linarith

private lemma disjoint_pairs {N : ℕ} (M : Finset (Finset (Fin N)))
    (hd : (M : Set (Finset (Fin N))).PairwiseDisjoint id)
    (hne : ∀ t ∈ M, t.Nonempty) (hs : ∀ t ∈ M, t.card ≤ 2) :
    M.card ≤ N ∧ ∃ p : M × Bool → Bool × Fin N, Function.Injective p ∧
      ∀ (t : M) (y : Fin N → Bool),
        xor ((p (t,false)).1 && y (p (t,false)).2)
          ((p (t,true)).1 && y (p (t,true)).2) =
            decide (Odd (t.val.filter fun j => y j = true).card) := by
  classical
  choose u v huv hu hv hpar using fun t : M => pair_rep t.val
    (hne t.val t.property) (hs t.val t.property)
  let p : M × Bool → Bool × Fin N := fun tb => if tb.2 then v tb.1 else u tb.1
  have hmem (tb : M × Bool) : (p tb).2 ∈ tb.1.val := by
    rcases tb with ⟨t,b⟩
    cases b <;> simp [p, hu, hv]
  have howner (tb sb : M × Bool) (he : (p tb).2 = (p sb).2) : tb.1 = sb.1 := by
    by_contra h
    have hd' : Disjoint tb.1.val sb.1.val := hd tb.1.property sb.1.property
      (fun h' => h (Subtype.ext h'))
    exact Finset.disjoint_left.mp hd' (hmem tb) (he ▸ hmem sb)
  have hp : Function.Injective p := by
    rintro ⟨t,b⟩ ⟨s,c⟩ he
    have ht : t = s := howner (t,b) (s,c) (congrArg Prod.snd he)
    subst s
    have hb : b = c := by
      cases b <;> cases c
      · rfl
      · exact False.elim (huv t (by simpa [p] using he))
      · exact False.elim (huv t (by simpa [p] using he.symm))
      · rfl
    subst c
    rfl
  have huinj : Function.Injective (fun t : M => (u t).2) := by
    intro t s he
    exact howner (t,false) (s,false) he
  have hc := Fintype.card_le_of_injective _ huinj
  simp only [Fintype.card_coe, Fintype.card_fin] at hc
  exact ⟨hc,p,hp,fun t y => by simpa [p] using hpar t y⟩



private lemma family_success {n N m : ℕ} (hN : 1 ≤ N)
    (g : Bool × Fin N → Qubits m) (hg : Function.Injective g)
    (C : (Fin n → Bool) → (Fin N → Bool)) (i : Fin n)
    (η κ : ℝ) (hκ : 0 < κ) (M : Finset (Finset (Fin N)))
    (hd : (M : Set (Finset (Fin N))).PairwiseDisjoint id)
    (hs : ∀ t ∈ M, t.card ≤ 2) (hc : η * (N:ℝ) ≤ M.card)
    (a : Finset (Fin N) → Bool)
    (ha : ∀ t ∈ M, 1/2 + κ ≤
      ((Finset.univ.filter fun x : Fin n → Bool =>
        x i = xor (a t) (decide (Odd (t.filter fun j => C x j = true).card))).card : ℝ) /
          (2:ℝ)^n) :
    ∃ A : Matrix (Qubits m) (Qubits m) ℂ, IsEffect A ∧
      ((2:ℝ)^n)⁻¹ * ∑ x : Fin n → Bool,
        (if x i then effectProb A ((2*(N:ℝ))⁻¹ • rank
          (phase g (fun bj => bj.1 && C x bj.2)) (phase g (fun bj => bj.1 && C x bj.2)))
        else 1 - effectProb A ((2*(N:ℝ))⁻¹ • rank
          (phase g (fun bj => bj.1 && C x bj.2)) (phase g (fun bj => bj.1 && C x bj.2)))) ≥
        1/2 + η*κ := by
  classical
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : (0:ℝ) < 2^n := by positivity
  have hne (t) (ht : t ∈ M) : t.Nonempty := correlated_nonempty i C κ hκ t (a t) (ha t ht)
  obtain ⟨hcard,p,hp,hpar⟩ := disjoint_pairs M hd hne hs
  let z : M → ℝ := fun t => -sgn (a t)
  obtain ⟨A,hA,hform⟩ := match_effect (fun tb => g (p tb)) (hg.comp hp) z
    (fun t => by simpa [z] using sgn_sq (a t))
  let ψ : (Fin n → Bool) → Qubits m → ℂ := fun x => phase g (fun bj => bj.1 && C x bj.2)
  let ρ : (Fin n → Bool) → Matrix (Qubits m) (Qubits m) ℂ := fun x =>
    (2*(N:ℝ))⁻¹ • rank (ψ x) (ψ x)
  let pred : M → (Fin n → Bool) → Bool := fun t x =>
    xor (a t) (decide (Odd (t.val.filter fun j => C x j = true).card))
  let v : M → (Fin n → Bool) → ℝ := fun t x => z t *
    (ψ x (g (p (t,false))) * conj (ψ x (g (p (t,true))))).re
  have hprob (x : Fin n → Bool) :
      effectProb A (ρ x) = 1/2 + (2*(N:ℝ))⁻¹ * ∑ t : M, v t x := by
    have htrace : (rank (ψ x) (ψ x)).trace.re = 2*(N:ℝ) := by
      rw [show (rank (ψ x) (ψ x)).trace = Fintype.card (Bool × Fin N) from phase_trace g hg _]
      simp
    change effectProb A ((2*(N:ℝ))⁻¹ • rank (ψ x) (ψ x)) = _
    rw [prob_rsmul, hform, htrace]
    change (2*(N:ℝ))⁻¹ * (2*(N:ℝ)/2 + ∑ t : M, v t x) = _
    field_simp
    <;> ring
  have hsuccess (x : Fin n → Bool) :
      (if x i then effectProb A (ρ x) else 1-effectProb A (ρ x)) =
        1/2 + (N:ℝ)⁻¹ * ∑ t : M, ((if x i = pred t x then (1:ℝ) else 0)-1/2) := by
    have hterm (t : M) : (if x i then (1:ℝ) else -1) * v t x =
        2*((if x i = pred t x then (1:ℝ) else 0)-1/2) := by
      dsimp only [v, ψ, z, pred]
      simp only [phase_apply g hg, ← hpar t (C x)]
      cases hb : x i <;> cases ha : a t <;>
        cases h0 : (p (t,false)).1 && C x (p (t,false)).2 <;>
        cases h1 : (p (t,true)).1 && C x (p (t,true)).2 <;>
        norm_num [sgn, hb, ha, h0, h1]
    have he : (if x i then effectProb A (ρ x) else 1-effectProb A (ρ x)) =
        1/2 + (2*(N:ℝ))⁻¹ * ∑ t : M, (if x i then (1:ℝ) else -1) * v t x := by
      rw [hprob]
      cases hb : x i <;> simp only [hb, Bool.false_eq_true, ↓reduceIte, one_mul, neg_one_mul,
        Finset.sum_neg_distrib] <;> ring
    rw [he]
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    field_simp
    <;> ring
  have htbound (t : M) : (2:ℝ)^n * κ ≤
      ∑ x : Fin n → Bool, ((if x i = pred t x then (1:ℝ) else 0)-1/2) := by
    have h := (le_div_iff₀ hpow).mp (ha t.val t.property)
    have hcount : (∑ x : Fin n → Bool, if x i = pred t x then (1:ℝ) else 0) =
        ((Finset.univ.filter fun x : Fin n → Bool => x i = pred t x).card : ℝ) := by
      simp
    rw [Finset.sum_sub_distrib, hcount]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    dsimp only [pred] at *
    linarith
  have htot : (2:ℝ)^n * ((M.card:ℝ)*κ) ≤
      ∑ t : M, ∑ x : Fin n → Bool, ((if x i = pred t x then (1:ℝ) else 0)-1/2) := by
    calc
      _ = ∑ t : M, (2:ℝ)^n*κ := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun t _ => htbound t)
  have hsum : (∑ x : Fin n → Bool,
      (if x i then effectProb A (ρ x) else 1-effectProb A (ρ x))) =
      (2:ℝ)^n/2 + (N:ℝ)⁻¹ * ∑ t : M, ∑ x : Fin n → Bool,
        ((if x i = pred t x then (1:ℝ) else 0)-1/2) := by
    simp_rw [hsuccess]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
    simp
    <;> ring
  refine ⟨A,hA,?_⟩
  change ((2:ℝ)^n)⁻¹ * ∑ x : Fin n → Bool,
    (if x i then effectProb A (ρ x) else 1-effectProb A (ρ x)) ≥ _
  rw [hsum]
  have havg : ((2:ℝ)^n)⁻¹ * ((2:ℝ)^n/2 + (N:ℝ)⁻¹ *
      ∑ t : M, ∑ x : Fin n → Bool, ((if x i = pred t x then (1:ℝ) else 0)-1/2)) =
      1/2 + (N:ℝ)⁻¹ * ((2:ℝ)^n)⁻¹ *
        ∑ t : M, ∑ x : Fin n → Bool, ((if x i = pred t x then (1:ℝ) else 0)-1/2) := by ring_nf; simp [hpow.ne'] <;> ring
  rw [havg]
  calc
    _ ≥ 1/2 + (N:ℝ)⁻¹ * ((2:ℝ)^n)⁻¹ * ((2:ℝ)^n*((M.card:ℝ)*κ)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left htot (by positivity)) _
    _ = 1/2 + (N:ℝ)⁻¹ * ((M.card:ℝ)*κ) := by field_simp <;> ring
    _ ≥ 1/2 + η*κ := by
      apply add_le_add_right
      rw [← div_eq_inv_mul, le_div_iff₀ hNr]
      nlinarith [mul_le_mul_of_nonneg_right hc hκ.le]

end ParityQRAC

open ParityQRAC

theorem solution {n N : ℕ} (hn : 1 ≤ n) (hN : 1 ≤ N)
    (C : (Fin n → Bool) → (Fin N → Bool)) (η κ : ℝ)
    (hη : 0 < η) (hκ : 0 < κ)
    (hM : ∀ i : Fin n, ∃ M : Finset (Finset (Fin N)),
      (M : Set (Finset (Fin N))).PairwiseDisjoint id ∧
      (∀ t ∈ M, t.card ≤ 2) ∧ η * (N : ℝ) ≤ (M.card : ℝ) ∧
      ∃ a : Finset (Fin N) → Bool, ∀ t ∈ M,
        1 / 2 + κ ≤
          ((Finset.univ.filter fun x : Fin n → Bool =>
            x i = xor (a t) (decide (Odd (t.filter fun j => C x j = true).card))).card : ℝ) /
              (2 : ℝ) ^ n) :
    η * κ ≤ 1 / 2 ∧
      ∃ (m : ℕ) (ρ : (Fin n → Bool) → Matrix (Qubits m) (Qubits m) ℂ),
        (m : ℝ) ≤ Real.logb 2 (N : ℝ) + 2 ∧ IsQRAC ρ (1 / 2 + η * κ) := by
  classical
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : (0:ℝ) < 2^n := by positivity
  have hbudget : η*κ ≤ 1/2 := by
    let i : Fin n := ⟨0,by omega⟩
    obtain ⟨M,hd,hs,hc,a,ha⟩ := hM i
    have hne (t) (ht : t ∈ M) : t.Nonempty := correlated_nonempty i C κ hκ t (a t) (ha t ht)
    have hcard := (disjoint_pairs M hd hne hs).1
    have hcardr : (M.card:ℝ) ≤ N := by exact_mod_cast hcard
    have hη1 : η ≤ 1 := by nlinarith
    have hMpos : 0 < M.card := by
      have hr : (0:ℝ) < M.card := lt_of_lt_of_le (mul_pos hη hNr) hc
      exact_mod_cast hr
    obtain ⟨t,ht⟩ := Finset.card_pos.mp hMpos
    have hcount : ((Finset.univ.filter fun x : Fin n → Bool =>
        x i = xor (a t) (decide (Odd (t.filter fun j => C x j = true).card))).card : ℝ) ≤
          (2:ℝ)^n := by
      have h := Finset.card_le_card (Finset.filter_subset (s := Finset.univ)
        (p := fun x : Fin n → Bool => x i = xor (a t)
          (decide (Odd (t.filter fun j => C x j = true).card))))
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
      exact_mod_cast h
    have hk : κ ≤ 1/2 := by
      have h := (ha t ht).trans ((div_le_one hpow).mpr hcount)
      linarith
    exact (mul_le_mul_of_nonneg_right hη1 hκ.le).trans (by simpa using hk)
  letI : Nonempty (Fin N) := ⟨⟨0,by omega⟩⟩
  let m := Nat.clog 2 (2*N)
  have hsize : Fintype.card (Bool × Fin N) ≤ 2^m := by
    simpa [m] using Nat.le_pow_clog (by decide : 1 < 2) (2*N)
  let g : Bool × Fin N → Qubits m := fun b =>
    (bitsEquivFin m).symm (Fin.castLE hsize (Fintype.equivFin (Bool × Fin N) b))
  have hg : Function.Injective g := by
    intro u v h
    exact (Fintype.equivFin (Bool × Fin N)).injective
      (Fin.castLE_injective hsize ((bitsEquivFin m).symm.injective h))
  let ρ : (Fin n → Bool) → Matrix (Qubits m) (Qubits m) ℂ := fun x =>
    (2*(N:ℝ))⁻¹ • rank (phase g (fun bj => bj.1 && C x bj.2))
      (phase g (fun bj => bj.1 && C x bj.2))
  refine ⟨hbudget,m,ρ,qubit_budget hN,?_,?_⟩
  · intro x
    simpa only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_ofNat] using phase_density g hg (fun bj => bj.1 && C x bj.2)
  · intro i
    obtain ⟨M,hd,hs,hc,a,ha⟩ := hM i
    exact family_success hN g hg C i η κ hκ M hd hs hc a ha
