-- Prove2me | solution 1 for ValuationSubring.forall_smul_completion_eq_self_iff_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/37fa6936-e971-540e-a246-02a3ed0d7dd4

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ValuationSubring_CompletionDecompositionAction
import Theorems.Thm_ValuationSubring_valuation_map_eq_of_mem_decompositionSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_forall_smul_completion_eq_self_iff_mem_closure

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Polynomial

namespace AXV

variable {Ω Γ₀ : Type*} [Field Ω] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation Ω Γ₀)

lemma map_natCast_le_one (n : ℕ) : v (n : Ω) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (v.map_add _ _).trans (max_le ih (by rw [v.map_one]))

lemma map_intCast_le_one (z : ℤ) : v (z : Ω) ≤ 1 := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [Int.cast_natCast]; exact map_natCast_le_one v n
  · rw [Int.cast_neg, Int.cast_natCast, Valuation.map_neg]; exact map_natCast_le_one v n

variable (p : ℕ) [hp : Fact p.Prime]

lemma map_natCast_eq_one (hvp : v (p : Ω) < 1) {N : ℕ} (h : ¬ p ∣ N) : v (N : Ω) = 1 := by
  have hcop : Nat.Coprime N p := (Nat.Prime.coprime_iff_not_dvd hp.out).mpr h |>.symm
  have hbez := Nat.Coprime.gcd_eq_one hcop
  have hint : ((Nat.gcd N p : ℕ) : ℤ) = N * Nat.gcdA N p + p * Nat.gcdB N p := Nat.gcd_eq_gcd_ab N p
  rw [hbez] at hint
  have hΩ : (1 : Ω) = (N : Ω) * (Nat.gcdA N p : Ω) + (p : Ω) * (Nat.gcdB N p : Ω) := by
    have := congrArg (fun z : ℤ => (z : Ω)) hint
    simpa using this
  refine le_antisymm (map_natCast_le_one v N) ?_
  by_contra hlt
  push Not at hlt
  have h1 : v ((N : Ω) * (Nat.gcdA N p : Ω)) < 1 := by
    rw [map_mul]
    calc v (N : Ω) * v (Nat.gcdA N p : Ω) ≤ v (N : Ω) * 1 :=
          mul_le_mul_right (map_intCast_le_one v _) _
      _ < 1 := by rw [mul_one]; exact hlt
  have h2 : v ((p : Ω) * (Nat.gcdB N p : Ω)) < 1 := by
    rw [map_mul]
    calc v (p : Ω) * v (Nat.gcdB N p : Ω) ≤ v (p : Ω) * 1 :=
          mul_le_mul_right (map_intCast_le_one v _) _
      _ < 1 := by rw [mul_one]; exact hvp
  have := v.map_add_lt h1 h2
  rw [← hΩ, v.map_one] at this
  exact lt_irrefl _ this

lemma map_p_le_map_natCast (hvp : v (p : Ω) < 1) {N : ℕ} (hN : N ≠ 0) (h : ¬ p ^ 2 ∣ N) :
    v (p : Ω) ≤ v (N : Ω) := by
  by_cases hd : p ∣ N
  · obtain ⟨u, rfl⟩ := hd
    have hu : ¬ p ∣ u := by
      rintro ⟨w, rfl⟩
      exact h ⟨w, by ring⟩
    rw [Nat.cast_mul, map_mul, map_natCast_eq_one v p hvp hu, mul_one]
  · rw [map_natCast_eq_one v p hvp hd]
    exact hvp.le

omit hp in
lemma map_multiset_sum_le (t : Multiset Ω) (B : Γ₀) (h : ∀ x ∈ t, v x ≤ B) : v t.sum ≤ B := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.sum_cons]
    refine (v.map_add _ _).trans (max_le ?_ ?_)
    · exact h a (Multiset.mem_cons_self a t)
    · exact ih fun x hx => h x (Multiset.mem_cons_of_mem hx)

omit hp in
lemma map_multiset_prod_eq (t : Multiset Ω) : v t.prod = (t.map fun x => v x).prod :=
  map_multiset_prod v t

omit hp in
lemma map_multiset_prod_le (t : Multiset Ω) (δ : Γ₀) (h : ∀ x ∈ t, v x ≤ δ) :
    v t.prod ≤ δ ^ Multiset.card t := by
  rw [map_multiset_prod_eq, ← Multiset.card_map (fun x => v x) t]
  refine Multiset.prod_le_pow_card _ _ ?_
  intro y hy
  rw [Multiset.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact h x hx

omit hp in
lemma map_esymm_le (s : Multiset Ω) (δ : Γ₀) (h : ∀ x ∈ s, v x ≤ δ) (m : ℕ) :
    v (s.esymm m) ≤ δ ^ m := by
  unfold Multiset.esymm
  refine map_multiset_sum_le v _ _ ?_
  intro x hx
  rw [Multiset.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [Multiset.mem_powersetCard] at hu
  rw [← hu.2]
  exact map_multiset_prod_le v u δ fun y hy => h y (Multiset.mem_of_le hu.1 hy)

omit hp in
lemma taylor_multiset_prod (r : Ω) (t : Multiset (Polynomial Ω)) :
    taylor r t.prod = (t.map fun q => taylor r q).prod := by
  induction t using Multiset.induction with
  | empty => simp [taylor_one]
  | cons a t ih => rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, taylor_mul, ih]

omit hp in
lemma taylor_prod_X_sub_C (r : Ω) (s : Multiset Ω) :
    taylor r ((s.map fun a => X - C a).prod) = ((s.map fun a => a - r).map fun a => X - C a).prod := by
  rw [taylor_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp only [Function.comp_apply, map_sub, taylor_X, taylor_C]
  ring

lemma hasseDeriv_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (k : ℕ)
    (f : R[X]) : hasseDeriv k (f.map φ) = (hasseDeriv k f).map φ := by
  ext n
  simp [hasseDeriv_coeff, coeff_map]

variable [IsAlgClosed Ω]

omit hp in

theorem key (f : (Polynomial Ω)) (hf : f.Monic) (α : Ω) (δ : Γ₀)
    (hroots : ∀ β ∈ f.roots, v (β - α) ≤ δ) (j : ℕ) (hj : j < f.natDegree)
    (hN : (f.natDegree.choose j : Ω) ≠ 0) :
    ∃ β ∈ (hasseDeriv j f).roots,
      v (f.natDegree.choose j : Ω) * v (β - α) ^ (f.natDegree - j) ≤ δ ^ (f.natDegree - j) := by
  classical
  set n := f.natDegree with hn
  set m := n - j with hm
  have hm0 : m ≠ 0 := by omega
  have hmj : m + j = n := by omega

  have hsplit : f = (f.roots.map fun a => X - C a).prod :=
    (IsAlgClosed.splits f).eq_prod_roots_of_monic hf
  have hcard : f.roots.card = n := ((IsAlgClosed.splits f).natDegree_eq_card_roots).symm
  set s : Multiset Ω := f.roots.map fun a => a - α with hs
  have hscard : s.card = n := by rw [hs, Multiset.card_map, hcard]
  have hsδ : ∀ x ∈ s, v x ≤ δ := by
    intro x hx
    rw [hs, Multiset.mem_map] at hx
    obtain ⟨β, hβ, rfl⟩ := hx
    exact hroots β hβ

  have htaylor : taylor α f = (s.map fun a => X - C a).prod := by
    conv_lhs => rw [hsplit]
    rw [taylor_prod_X_sub_C]
  have hcoeff : (taylor α f).coeff j = (-1) ^ (n - j) * s.esymm (n - j) := by
    rw [htaylor, Multiset.prod_X_sub_C_coeff s (by rw [hscard]; omega), hscard]
  set g := hasseDeriv j f with hg
  have heval_le : v (g.eval α) ≤ δ ^ m := by
    rw [hg, ← taylor_coeff, hcoeff, map_mul, map_pow, Valuation.map_neg, v.map_one, one_pow, one_mul,
      ← hm]
    exact map_esymm_le v s δ hsδ m

  have hgcoeff : g.coeff m = (n.choose j : Ω) := by
    rw [hg, hasseDeriv_coeff, hmj]
    have : f.coeff n = 1 := hf.coeff_natDegree
    rw [this, mul_one]
  have hgdeg : g.natDegree = m := by
    refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [hgcoeff]; exact hN))
    rw [hg, hm, hn]
    exact natDegree_hasseDeriv_le f j
  have hglead : g.leadingCoeff = (n.choose j : Ω) := by
    rw [leadingCoeff, hgdeg, hgcoeff]
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, leadingCoeff_zero] at hglead
    exact hN hglead.symm
  have hgsplit : g = C (n.choose j : Ω) * (g.roots.map fun a => X - C a).prod := by
    rw [← hglead]
    exact (IsAlgClosed.splits g).eq_prod_roots
  have hgcard : g.roots.card = m := by
    rw [← hgdeg]; exact ((IsAlgClosed.splits g).natDegree_eq_card_roots).symm

  have hevalprod : g.eval α = (n.choose j : Ω) * (g.roots.map fun β => α - β).prod := by
    conv_lhs => rw [hgsplit]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    congr 1
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun β _ => ?_)
    simp
  have hnormprod : v (n.choose j : Ω) * (g.roots.map fun β => v (α - β)).prod ≤ δ ^ m := by
    have := heval_le
    rw [hevalprod, map_mul, map_multiset_prod_eq, Multiset.map_map] at this
    exact this

  have hne : g.roots.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty, ← Multiset.card_pos, hgcard]
    exact Nat.pos_of_ne_zero hm0
  obtain ⟨β₀, hβ₀, hmin⟩ := Finset.exists_min_image g.roots.toFinset (fun β => v (α - β)) hne
  rw [Multiset.mem_toFinset] at hβ₀
  refine ⟨β₀, hβ₀, ?_⟩
  have hpow : v (α - β₀) ^ m ≤ (g.roots.map fun β => v (α - β)).prod := by
    have := Multiset.pow_card_le_prod (s := g.roots.map fun β => v (α - β)) (a := v (α - β₀))
      (by
        intro x hx
        rw [Multiset.mem_map] at hx
        obtain ⟨β, hβ, rfl⟩ := hx
        exact hmin β (Multiset.mem_toFinset.mpr hβ))
    rwa [Multiset.card_map, hgcard] at this
  rw [Valuation.map_sub_swap]
  exact (mul_le_mul_right hpow _).trans hnormprod

section Galois

variable {F : Type*} [Field F] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
variable (K : IntermediateField F Ω)

local notation "Γ" => (Ω ≃ₐ[F] Ω)

scoped instance isAlgClosureK : IsAlgClosure K Ω :=
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := F) K⟩

scoped instance normalK : Normal K Ω := IsAlgClosure.normal K Ω

omit hp in
lemma isIntegralK (α : Ω) : IsIntegral K α :=
  (Algebra.IsAlgebraic.isAlgebraic (R := K) α).isIntegral

omit hp in

lemma roots_minpoly_map_sub_le (α : Ω) (δ : Γ₀)
    (h : ∀ σ : Γ, σ ∈ K.fixingSubgroup → v (σ α - α) ≤ δ) :
    ∀ β ∈ ((minpoly K α).map (algebraMap K Ω)).roots, v (β - α) ≤ δ := by
  intro β hβ
  have hint := isIntegralK K α
  have hmon : ((minpoly K α).map (algebraMap K Ω)).Monic := (minpoly.monic hint).map _
  rw [mem_roots hmon.ne_zero, IsRoot.def, eval_map, ← aeval_def] at hβ
  have hmin : minpoly K α = minpoly K β :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hβ (minpoly.monic hint)
  have horb : β ∈ MulAction.orbit (Ω ≃ₐ[K] Ω) α :=
    (Normal.minpoly_eq_iff_mem_orbit Ω).mp hmin.symm
  obtain ⟨τ, hτ⟩ := horb
  set σ : Γ := τ.restrictScalars F with hσ
  have hσK : σ ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change τ x = x
    exact τ.commutes ⟨x, hx⟩
  have hσα : σ α = β := hτ
  rw [← hσα]
  exact h σ hσK

omit hp in

lemma natDegree_minpoly_le_of_mem_roots_hasseDeriv (α : Ω) (j : ℕ)
    (hj : j < (minpoly K α).natDegree)
    (hN : ((minpoly K α).natDegree.choose j : Ω) ≠ 0)
    (β : Ω) (hβ : β ∈ (hasseDeriv j ((minpoly K α).map (algebraMap K Ω))).roots) :
    (minpoly K β).natDegree ≤ (minpoly K α).natDegree - j := by
  set gK := hasseDeriv j (minpoly K α) with hgK
  have hmap : hasseDeriv j ((minpoly K α).map (algebraMap K Ω)) = gK.map (algebraMap K Ω) :=
    hasseDeriv_map _ _ _
  have hint := isIntegralK K α

  have hcoeff : gK.coeff ((minpoly K α).natDegree - j) = ((minpoly K α).natDegree.choose j : K) := by
    rw [hgK, hasseDeriv_coeff, Nat.sub_add_cancel hj.le, (minpoly.monic hint).coeff_natDegree,
      mul_one]
  have hgK0 : gK ≠ 0 := by
    intro h0
    have := hcoeff
    rw [h0, coeff_zero] at this
    have hc : ((minpoly K α).natDegree.choose j : K) ≠ 0 := by
      intro hc
      apply hN
      have := congrArg (algebraMap K Ω) hc
      simpa using this
    exact hc this.symm
  have hmap0 : gK.map (algebraMap K Ω) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero]
  rw [hmap, mem_roots hmap0, IsRoot.def, eval_map, ← aeval_def] at hβ
  have hdeg := minpoly.degree_le_of_ne_zero K β hgK0 hβ
  refine (natDegree_le_natDegree hdeg).trans ?_
  rw [hgK]
  exact natDegree_hasseDeriv_le _ _

omit hp in

lemma map_conj_sub_le (hK : ∀ σ : Γ, σ ∈ K.fixingSubgroup → ∀ x : Ω, v (σ x) = v x)
    (α β : Ω) (δ ε : Γ₀)
    (h : ∀ σ : Γ, σ ∈ K.fixingSubgroup → v (σ α - α) ≤ δ) (hβ : v (β - α) ≤ ε) (hδε : δ ≤ ε) :
    ∀ σ : Γ, σ ∈ K.fixingSubgroup → v (σ β - β) ≤ ε := by
  intro σ hσ
  have hsplit : σ β - β = σ (β - α) + ((σ α - α) + (α - β)) := by
    rw [map_sub]; abel
  rw [hsplit]
  refine (v.map_add _ _).trans (max_le ?_ ?_)
  · rw [hK σ hσ]; exact hβ
  · refine (v.map_add _ _).trans (max_le ((h σ hσ).trans hδε) ?_)
    rw [Valuation.map_sub_swap]; exact hβ

end Galois

lemma choose_prime_pow_modEq (L : ℕ) : ∀ n : ℕ, n.choose (p ^ L) ≡ n / p ^ L [MOD p] := by
  induction L with
  | zero => intro n; rw [pow_zero, Nat.choose_one_right, Nat.div_one]
  | succ L ih =>
    intro n
    have h1 := @Choose.choose_modEq_choose_mod_mul_choose_div_nat n (p ^ (L + 1)) p hp
    have hk : p ^ (L + 1) % p = 0 := by
      rw [pow_succ]; exact Nat.mul_mod_left _ _
    have hk' : p ^ (L + 1) / p = p ^ L := by
      rw [pow_succ, Nat.mul_div_cancel _ hp.out.pos]
    rw [hk, hk', Nat.choose_zero_right, one_mul] at h1
    refine h1.trans ?_
    have := ih (n / p)
    rwa [Nat.div_div_eq_div_mul, mul_comm, ← pow_succ] at this

lemma not_dvd_choose_prime_pow {n L : ℕ} (h1 : p ^ L ≤ n) (h2 : n < p ^ (L + 1)) :
    ¬ p ∣ n.choose (p ^ L) := by
  intro hd
  have hmod := choose_prime_pow_modEq p L n
  have hq1 : 1 ≤ n / p ^ L := (Nat.le_div_iff_mul_le (pow_pos hp.out.pos L)).mpr (by simpa using h1)
  have hq2 : n / p ^ L < p := by
    rw [Nat.div_lt_iff_lt_mul (pow_pos hp.out.pos L)]
    calc n < p ^ (L + 1) := h2
      _ = p * p ^ L := by rw [pow_succ, mul_comm]
  have h0 : n.choose (p ^ L) % p = 0 := Nat.mod_eq_zero_of_dvd hd
  have : (n / p ^ L) % p = 0 := by
    have := hmod
    rw [Nat.ModEq, h0] at this
    exact this.symm
  rw [Nat.mod_eq_of_lt hq2] at this
  omega

lemma not_sq_dvd_choose_prime_pow_pred {L : ℕ} (hL : 1 ≤ L) :
    ¬ p ^ 2 ∣ (p ^ L).choose (p ^ (L - 1)) := by
  have hprime : Prime p := Nat.prime_iff.mp hp.out
  have hk : p ^ (L - 1) ≤ p ^ L := Nat.pow_le_pow_right hp.out.pos (Nat.sub_le L 1)
  have hk0 : p ^ (L - 1) ≠ 0 := (pow_pos hp.out.pos _).ne'
  have hem := Nat.Prime.emultiplicity_choose_prime_pow hp.out hk hk0
  rw [multiplicity_pow_self_of_prime hprime] at hem
  have hL1 : L - (L - 1) = 1 := by omega
  rw [hL1] at hem
  have := (emultiplicity_eq_coe.mp hem).2
  simpa using this

lemma sum_pow_le_two_mul_pow (K : ℕ) : ∑ i ∈ Finset.range (K + 1), p ^ i ≤ 2 * p ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have h2 : 2 * p ^ K ≤ p ^ (K + 1) := by
      rw [pow_succ, mul_comm]
      exact Nat.mul_le_mul_left _ hp.out.two_le
    omega

noncomputable def piSeq (i : ℕ) : Ω :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (p : Ω) (pow_pos hp.out.pos i))

lemma piSeq_pow (i : ℕ) : (piSeq p i : Ω) ^ (p ^ i) = p :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (p : Ω) (pow_pos hp.out.pos i))

noncomputable def cst (L : ℕ) : Ω := ∏ i ∈ Finset.range L, piSeq p i

lemma cst_zero : (cst p 0 : Ω) = 1 := by simp [cst]

lemma cst_succ (L : ℕ) : (cst p (L + 1) : Ω) = cst p L * piSeq p L := by
  rw [cst, Finset.prod_range_succ, cst]

lemma map_piSeq_le_one (hvp : v (p : Ω) < 1) (i : ℕ) : v (piSeq p i : Ω) ≤ 1 := by
  have h : v (piSeq p i : Ω) ^ (p ^ i) < 1 ^ (p ^ i) := by
    rw [← map_pow, piSeq_pow, one_pow]; exact hvp
  exact (lt_of_pow_lt_pow_left₀ _ zero_le_one h).le

lemma piSeq_ne_zero (hp0 : (p : Ω) ≠ 0) (i : ℕ) : (piSeq p i : Ω) ≠ 0 := by
  intro h
  have := piSeq_pow p i (Ω := Ω)
  rw [h, zero_pow (pow_pos hp.out.pos i).ne'] at this
  exact hp0 this.symm

lemma map_cst_le_one (hvp : v (p : Ω) < 1) (L : ℕ) : v (cst p L : Ω) ≤ 1 := by
  induction L with
  | zero => rw [cst_zero, v.map_one]
  | succ L ih =>
    rw [cst_succ, map_mul]
    calc v (cst p L : Ω) * v (piSeq p L : Ω) ≤ v (cst p L : Ω) * 1 :=
          mul_le_mul_right (map_piSeq_le_one v p hvp L) _
      _ ≤ 1 := by rw [mul_one]; exact ih

lemma map_cst_anti (hvp : v (p : Ω) < 1) {L L' : ℕ} (h : L ≤ L') :
    v (cst p L' : Ω) ≤ v (cst p L : Ω) := by
  induction L', h using Nat.le_induction with
  | base => exact le_rfl
  | succ L' hLL' ih =>
    rw [cst_succ, map_mul]
    calc v (cst p L' : Ω) * v (piSeq p L' : Ω) ≤ v (cst p L' : Ω) * 1 :=
          mul_le_mul_right (map_piSeq_le_one v p hvp L') _
      _ ≤ v (cst p L : Ω) := by rw [mul_one]; exact ih

lemma map_cst_succ_pow (K : ℕ) :
    v (cst p (K + 1) : Ω) ^ (p ^ K) = v (p : Ω) ^ (∑ i ∈ Finset.range (K + 1), p ^ i) := by
  induction K with
  | zero =>
    rw [pow_zero, pow_one, Finset.sum_range_one, pow_zero, pow_one, cst_succ, cst_zero, one_mul]
    have h := piSeq_pow p 0 (Ω := Ω)
    rw [pow_zero, pow_one] at h
    rw [h]
  | succ K ih =>
    have hπ : v (piSeq p (K + 1) : Ω) ^ (p ^ (K + 1)) = v (p : Ω) := by
      rw [← map_pow, piSeq_pow]
    rw [cst_succ, map_mul, mul_pow, hπ, pow_succ p K, pow_mul, ih, ← pow_mul, ← pow_succ]
    congr 1
    rw [Finset.sum_range_succ' (fun i => p ^ i) (K + 1), pow_zero, Finset.sum_mul]
    refine congrArg (· + 1) (Finset.sum_congr rfl fun i _ => ?_)
    rw [pow_succ]

lemma map_p_sq_le_map_cst (hvp : v (p : Ω) < 1) (L : ℕ) : v ((p : Ω) ^ 2) ≤ v (cst p L : Ω) := by
  cases L with
  | zero =>
    rw [cst_zero, v.map_one, map_pow]
    exact pow_le_one' hvp.le 2
  | succ K =>
    have hM : p ^ K ≠ 0 := (pow_pos hp.out.pos K).ne'
    refine le_of_pow_le_pow_left₀ hM zero_le' ?_
    rw [map_cst_succ_pow, map_pow, ← pow_mul]
    exact pow_le_pow_right_of_le_one' hvp.le (sum_pow_le_two_mul_pow p K)

section Main

variable {F : Type*} [Field F] [Algebra F Ω] [Algebra.IsAlgebraic F Ω]
variable (K : IntermediateField F Ω)

local notation "Γ" => (Ω ≃ₐ[F] Ω)

theorem main (hvp : v (p : Ω) < 1) (hp0 : (p : Ω) ≠ 0)
    (hK : ∀ σ : Γ, σ ∈ K.fixingSubgroup → ∀ x : Ω, v (σ x) = v x) (n : ℕ) :
    ∀ (α : Ω) (δ : Γ₀),
    (minpoly K α).natDegree ≤ n →
    (∀ σ : Γ, σ ∈ K.fixingSubgroup → v (σ α - α) ≤ δ) →
      ∃ a ∈ K, v (cst p (Nat.log p n) * (α - a)) ≤ δ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α δ hdeg hconj
    have hint := isIntegralK K α
    set n₀ := (minpoly K α).natDegree with hn₀
    have hn₀pos : 0 < n₀ := minpoly.natDegree_pos hint

    by_cases h1 : n₀ = 1
    · have hα : α ∈ (algebraMap K Ω).range := minpoly.natDegree_eq_one_iff.mp h1
      obtain ⟨a, ha⟩ := hα
      refine ⟨(a : Ω), a.2, ?_⟩
      have : (a : Ω) = α := ha
      rw [this, sub_self, mul_zero, Valuation.map_zero]
      exact zero_le'
    have hn₀2 : 2 ≤ n₀ := by omega

    set L := Nat.log p n₀ with hL
    have hpL : p ^ L ≤ n₀ := Nat.pow_log_le_self p (by omega)
    have hn₀lt : n₀ < p ^ (L + 1) := Nat.lt_pow_succ_log_self hp.out.one_lt n₀
    have hlogn : L ≤ Nat.log p n := Nat.log_mono_right hdeg

    set f : (Polynomial Ω) := (minpoly K α).map (algebraMap K Ω) with hf
    have hfmon : f.Monic := (minpoly.monic hint).map _
    have hfdeg : f.natDegree = n₀ := (minpoly.monic hint).natDegree_map _
    have hroots : ∀ β ∈ f.roots, v (β - α) ≤ δ := roots_minpoly_map_sub_le v K α δ hconj

    have cont : ∀ (m : ℕ) (π : Ω), 0 < m → m < n₀ → v π ≤ 1 → π ≠ 0 →
        (n₀.choose (n₀ - m) : Ω) ≠ 0 →
        v π ^ m ≤ v (n₀.choose (n₀ - m) : Ω) →
        v (cst p L : Ω) ≤ v (cst p (Nat.log p m) * π : Ω) →
        ∃ a ∈ K, v (cst p (Nat.log p n) * (α - a)) ≤ δ := by
      intro m π hm0 hmn hπ1 hπ0 hN hNπ hcst
      set j := n₀ - m with hj
      have hjlt : j < f.natDegree := by rw [hfdeg]; omega
      have hmj : f.natDegree - j = m := by rw [hfdeg]; omega
      have hNf : (f.natDegree.choose j : Ω) ≠ 0 := by rw [hfdeg]; exact hN
      obtain ⟨β, hβ, hβle⟩ := key v f hfmon α δ hroots j hjlt hNf
      rw [hmj, hfdeg] at hβle
      have hvπ0 : v π ≠ 0 := (Valuation.ne_zero_iff v).mpr hπ0
      have hvπpos : 0 < v π := zero_lt_iff.mpr hvπ0

      have hβπ : v (π * (β - α)) ≤ δ := by
        refine le_of_pow_le_pow_left₀ hm0.ne' zero_le' ?_
        rw [map_mul, mul_pow]
        exact (mul_le_mul_left hNπ _).trans hβle

      set δ' : Γ₀ := (v π)⁻¹ * δ with hδ'
      have hπδ' : v π * δ' = δ := by rw [hδ', mul_inv_cancel_left₀ hvπ0]
      have hβδ' : v (β - α) ≤ δ' := by
        have : v (β - α) = (v π)⁻¹ * (v π * v (β - α)) := by rw [inv_mul_cancel_left₀ hvπ0]
        rw [this, hδ']
        refine mul_le_mul_right ?_ _
        rw [← map_mul]; exact hβπ
      have hδδ' : δ ≤ δ' := by
        have : δ = (v π)⁻¹ * (v π * δ) := by rw [inv_mul_cancel_left₀ hvπ0]
        rw [this, hδ']
        exact mul_le_mul_right (mul_le_of_le_one_left' hπ1) _

      have hβdeg : (minpoly K β).natDegree ≤ m := by
        have := natDegree_minpoly_le_of_mem_roots_hasseDeriv K α j (by omega)
          (by rw [← hn₀]; exact hN) β (by rw [← hf]; exact hβ)
        omega

      have hβconj := map_conj_sub_le v K hK α β δ δ' hconj hβδ' hδδ'

      have hmn' : m < n := lt_of_lt_of_le hmn hdeg
      obtain ⟨a, haK, ha⟩ := ih m hmn' β δ' hβdeg hβconj
      refine ⟨a, haK, ?_⟩

      have h2 : v (cst p (Nat.log p m) * π * (β - a)) ≤ δ := by
        rw [mul_right_comm, map_mul, ← hπδ', mul_comm (v π)]
        exact mul_le_mul_left ha _

      have h1 : v (cst p (Nat.log p m) * π * (α - β)) ≤ δ := by
        rw [mul_assoc, map_mul]
        have : v (π * (α - β)) = v (π * (β - α)) := by
          rw [map_mul, map_mul, Valuation.map_sub_swap]
        rw [this]
        calc v (cst p (Nat.log p m) : Ω) * v (π * (β - α)) ≤ 1 * δ :=
              mul_le_mul' (map_cst_le_one v p hvp _) hβπ
          _ = δ := one_mul δ
      have h12 : v (cst p (Nat.log p m) * π * (α - a)) ≤ δ := by
        have hsplit : cst p (Nat.log p m) * π * (α - a) =
            cst p (Nat.log p m) * π * (α - β) + cst p (Nat.log p m) * π * (β - a) := by ring
        rw [hsplit]
        exact (v.map_add _ _).trans (max_le h1 h2)
      calc v (cst p (Nat.log p n) * (α - a)) = v (cst p (Nat.log p n) : Ω) * v (α - a) := map_mul _ _ _
        _ ≤ v (cst p L : Ω) * v (α - a) := mul_le_mul_left (map_cst_anti v p hvp hlogn) _
        _ ≤ v (cst p (Nat.log p m) * π : Ω) * v (α - a) := mul_le_mul_left hcst _
        _ = v (cst p (Nat.log p m) * π * (α - a)) := (map_mul _ _ _).symm
        _ ≤ δ := h12
    by_cases hcase : p ^ L < n₀
    ·
      have hchoose : n₀.choose (n₀ - p ^ L) = n₀.choose (p ^ L) := Nat.choose_symm hpL
      have hvN : v ((n₀.choose (n₀ - p ^ L) : ℕ) : Ω) = 1 := by
        rw [hchoose]
        exact map_natCast_eq_one v p hvp (not_dvd_choose_prime_pow p hpL hn₀lt)
      refine cont (p ^ L) 1 (pow_pos hp.out.pos L) hcase (by rw [v.map_one]) one_ne_zero ?_ ?_ ?_
      · exact (Valuation.ne_zero_iff v).mp (by rw [hvN]; exact one_ne_zero)
      · rw [v.map_one, one_pow, hvN]
      · rw [mul_one, Nat.log_pow hp.out.one_lt]
    ·
      have hn₀eq : n₀ = p ^ L := le_antisymm (not_lt.mp hcase) hpL
      have hL1 : 1 ≤ L := by
        by_contra hL0
        push Not at hL0
        have : L = 0 := by omega
        rw [this, pow_zero] at hn₀eq
        omega
      set m := p ^ (L - 1) with hm
      have hm0 : 0 < m := pow_pos hp.out.pos _
      have hmn : m < n₀ := by
        rw [hn₀eq, hm]
        exact Nat.pow_lt_pow_right hp.out.one_lt (by omega)
      have hmle : m ≤ n₀ := hmn.le
      have hNnat : ¬ p ^ 2 ∣ n₀.choose m := by
        rw [hn₀eq, hm]; exact not_sq_dvd_choose_prime_pow_pred p hL1
      have hNne : n₀.choose m ≠ 0 := (Nat.choose_pos hmle).ne'
      have hchoose : n₀.choose (n₀ - m) = n₀.choose m := Nat.choose_symm hmle
      have hvpN : v (p : Ω) ≤ v ((n₀.choose (n₀ - m) : ℕ) : Ω) := by
        rw [hchoose]; exact map_p_le_map_natCast v p hvp hNne hNnat
      have hvp0 : v (p : Ω) ≠ 0 := (Valuation.ne_zero_iff v).mpr hp0
      set π : Ω := piSeq p (L - 1) with hπ
      have hπm : π ^ m = p := piSeq_pow p (L - 1)
      refine cont m π hm0 hmn (map_piSeq_le_one v p hvp _) (piSeq_ne_zero p hp0 _) ?_ ?_ ?_
      · refine (Valuation.ne_zero_iff v).mp fun h0 => hvp0 ?_
        exact le_antisymm (h0 ▸ hvpN) zero_le'
      · rw [← map_pow, hπm]; exact hvpN
      · have hL' : L = (L - 1) + 1 := by omega
        rw [hm, Nat.log_pow hp.out.one_lt]
        conv_lhs => rw [hL', cst_succ]

end Main

end AXV
p2m_reactivate "P2MW.S_ValuationSubring_forall_smul_completion_eq_self_iff_mem_closure.AXV"

theorem AXV.exists_mem_map_pow_mul_sub_le
    {F Ω Γ₀ : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic F Ω]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation Ω Γ₀)
    (p : ℕ) (hp : p.Prime) (hvp : v (p : Ω) < 1)
    (L : IntermediateField F Ω)
    (hL : ∀ σ : Ω ≃ₐ[F] Ω, σ ∈ L.fixingSubgroup → ∀ x : Ω, v (σ x) = v x)
    (α : Ω) (δ : Γ₀)
    (hα : ∀ σ : Ω ≃ₐ[F] Ω, σ ∈ L.fixingSubgroup → v (σ α - α) ≤ δ) :
    ∃ a ∈ L, v ((p : Ω) ^ 2 * (α - a)) ≤ δ := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hp0 : (p : Ω) = 0
  · refine ⟨0, zero_mem L, ?_⟩
    rw [hp0, zero_pow two_ne_zero, zero_mul, Valuation.map_zero]
    exact zero_le'
  obtain ⟨a, haL, ha⟩ :=
    AXV.main v p L hvp hp0 hL ((minpoly L α).natDegree) α δ le_rfl hα
  refine ⟨a, haL, ?_⟩
  calc v ((p : Ω) ^ 2 * (α - a)) = v ((p : Ω) ^ 2) * v (α - a) := map_mul _ _ _
    _ ≤ v (AXV.cst p (Nat.log p (minpoly L α).natDegree) : Ω) * v (α - a) :=
        mul_le_mul_left (AXV.map_p_sq_le_map_cst v p hvp _) _
    _ = v (AXV.cst p (Nat.log p (minpoly L α).natDegree) * (α - a)) := (map_mul _ _ _).symm
    _ ≤ δ := ha

namespace ASTA

open UniformSpace

section Galois

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

theorem exists_mem_apply_eq [IsGalois k K] (H : Subgroup (K ≃ₐ[k] K)) (σ : K ≃ₐ[k] K)
    (hσ : σ ∈ (IntermediateField.fixedField H).fixingSubgroup) (x : K) :
    ∃ τ ∈ H, τ x = σ x := by
  let Hc : ClosedSubgroup (K ≃ₐ[k] K) :=
    ⟨H.topologicalClosure, Subgroup.isClosed_topologicalClosure H⟩
  have hle : (IntermediateField.fixedField H).fixingSubgroup ≤
      (IntermediateField.fixedField (Hc : Subgroup (K ≃ₐ[k] K))).fixingSubgroup :=
    IntermediateField.fixingSubgroup_antitone
      (IntermediateField.fixedField_le H.le_topologicalClosure)
  have hσc : σ ∈ (Hc : Subgroup (K ≃ₐ[k] K)) := by
    rw [← InfiniteGalois.fixingSubgroup_fixedField Hc]; exact hle hσ
  have hσcl : σ ∈ closure (H : Set (K ≃ₐ[k] K)) := by
    rw [← Subgroup.topologicalClosure_coe]; exact hσc
  have hopen : IsOpen {ρ : K ≃ₐ[k] K | ρ x = σ x} := by
    have h1 : {ρ : K ≃ₐ[k] K | ρ x = σ x} =
        (fun ρ => σ⁻¹ * ρ) ⁻¹' (MulAction.stabilizer (K ≃ₐ[k] K) x : Set (K ≃ₐ[k] K)) := by
      ext ρ
      simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
        MulAction.mem_stabilizer_iff, AlgEquiv.smul_def, AlgEquiv.mul_apply, AlgEquiv.aut_inv,
        AlgEquiv.symm_apply_eq]
    rw [h1]
    exact (stabilizer_isOpen_of_isIntegral x).preimage (continuous_const_mul σ⁻¹)
  obtain ⟨τ, hτ1, hτ2⟩ := mem_closure_iff.mp hσcl _ hopen rfl
  exact ⟨τ, hτ2, hτ1⟩

end Galois
p2m_reactivate "P2MW.S_ValuationSubring_forall_smul_completion_eq_self_iff_mem_closure.AXV"

section ValuedField

open MonoidWithZeroHom

variable {R : Type*} [Ring R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem mem_closure_of_forall [Valued R Γ₀] (S : Set R) (x : R)
    (h : ∀ γ : Γ₀, γ ≠ 0 → ∃ y ∈ S, Valued.v (y - x) < γ) : x ∈ closure S := by
  rw [mem_closure_iff_nhds]
  intro t ht
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ht
  obtain ⟨r, s, hr, hs, hrs⟩ := Valuation.exists_div_eq_of_unit (Valued.v (R := R)) γ
  have hs0 : Valued.v s ≠ 0 := hs.ne'
  obtain ⟨y, hyS, hy⟩ := h (Valued.v r / Valued.v s) (div_ne_zero hr.ne' hs0)
  refine ⟨y, hγ ?_, hyS⟩
  show Valued.v.restrict (y - x) < γ.1
  rw [← hrs, lt_div_iff₀ ((Valuation.restrict_pos_iff _ s).mpr hs), ← map_mul,
    Valuation.restrict_lt_iff, map_mul]
  rwa [lt_div_iff₀ (zero_lt_iff.mpr hs0)] at hy

variable {K : Type*} [Field K] [hv : Valued K Γ₀]

theorem exists_valued_coe_sub_lt (x : Completion K) (r : K) (hr : Valued.v r ≠ 0) :
    ∃ a : K, Valued.v ((a : Completion K) - x) < Valued.v r := by
  have hr' : (Valued.v : Valuation (Completion K) Γ₀).restrict (r : Completion K) ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, Valued.valuedCompletion_apply]; exact hr
  have hU : {y : Completion K | Valued.v.restrict (y - x) < (Units.mk0 _ hr').1} ∈ nhds x :=
    Valued.mem_nhds.mpr ⟨Units.mk0 _ hr', subset_rfl⟩
  obtain ⟨a, ha⟩ := Completion.denseRange_coe.mem_nhds hU
  refine ⟨a, ?_⟩
  have := ha
  rw [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff, Valued.valuedCompletion_apply]
    at this
  exact this

end ValuedField
p2m_reactivate "P2MW.S_ValuationSubring_forall_smul_completion_eq_self_iff_mem_closure.AXV"

local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩

local notation "ℚbar" => AlgebraicClosure ℚ

variable (A : ValuationSubring ℚbar) (H : Subgroup ↥(A.decompositionSubgroup ℚ))

local notation "C" => A.valuation.Completion
local notation "D" => (A.decompositionSubgroup ℚ)

theorem decompositionIsometric : A.DecompositionIsometric ℚ :=
  fun σ z => ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A σ.2 z

noncomputable def ι : ℚbar →+* C :=
  (Completion.coeRingHom (α := WithVal A.valuation)).comp (WithVal.equiv A.valuation).symm.toRingHom

theorem ι_apply (r : ℚbar) : ι A r = ((r : ℚbar) : C) := rfl

theorem valued_coe (r : ℚbar) : Valued.v ((r : ℚbar) : C) = A.valuation r := by
  show Valued.v (((WithVal.equiv A.valuation).symm r : WithVal A.valuation) : C) = _
  rw [Valued.valuedCompletion_apply]
  rfl

theorem smul_eq_self_of_mem_closure (x : C)
    (hx : x ∈ closure (((↑) : ℚbar → C) ''
      (IntermediateField.fixedField (H.map (A.decompositionSubgroup ℚ).subtype) : Set ℚbar)))
    (σ : ↥D) (hσ : σ ∈ H) : σ • x = x := by
  haveI : Fact (A.DecompositionIsometric ℚ) := ⟨decompositionIsometric A⟩
  have hclosed : IsClosed {y : C | σ • y = y} :=
    isClosed_eq (continuous_const_smul σ) continuous_id
  refine closure_minimal ?_ hclosed hx
  rintro _ ⟨l, hl, rfl⟩
  show σ • ((l : ℚbar) : C) = ((l : ℚbar) : C)
  rw [ValuationSubring.smul_completion_coe]
  have hσ' : (σ : ℚbar ≃ₐ[ℚ] ℚbar) ∈ H.map (A.decompositionSubgroup ℚ).subtype :=
    ⟨σ, hσ, rfl⟩
  rw [(IntermediateField.mem_fixedField_iff _ _).mp hl _ hσ']

theorem mem_closure_of_forall_smul_eq_self (p : ℕ) (hp : p.Prime) (hA : A.LiesOverPrime p) (x : C)
    (hx : ∀ σ : ↥D, σ ∈ H → σ • x = x) :
    x ∈ closure (((↑) : ℚbar → C) ''
      (IntermediateField.fixedField (H.map (A.decompositionSubgroup ℚ).subtype) : Set ℚbar)) := by
  haveI : Fact (A.DecompositionIsometric ℚ) := ⟨decompositionIsometric A⟩
  set H' : Subgroup (ℚbar ≃ₐ[ℚ] ℚbar) := H.map (A.decompositionSubgroup ℚ).subtype with hH'
  set L : IntermediateField ℚ ℚbar := IntermediateField.fixedField H' with hL

  have hG1 : ∀ σ : ℚbar ≃ₐ[ℚ] ℚbar, σ ∈ L.fixingSubgroup → ∀ z : ℚbar, ∃ τ ∈ H', τ z = σ z :=
    fun σ hσ z => exists_mem_apply_eq H' σ hσ z
  have hiso : ∀ σ : ℚbar ≃ₐ[ℚ] ℚbar, σ ∈ L.fixingSubgroup → ∀ z : ℚbar, A.valuation (σ z) = A.valuation z := by
    intro σ hσ z
    obtain ⟨τ, hτ, hτz⟩ := hG1 σ hσ z
    obtain ⟨τ₀, -, rfl⟩ := Subgroup.mem_map.mp hτ
    rw [← hτz]
    exact ValuationSubring.valuation_map_eq_of_mem_decompositionSubgroup A τ₀.2 z

  have hp0 : (p : ℚbar) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hvp0 : A.valuation (p : ℚbar) ≠ 0 := (Valuation.ne_zero_iff A.valuation).mpr hp0
  have hvp1 : A.valuation (p : ℚbar) < 1 := (ValuationSubring.mem_nonunits_iff A).mp hA

  apply mem_closure_of_forall
  intro γ hγ
  obtain ⟨r, hr⟩ := A.valuation_surjective (γ * A.valuation (p : ℚbar) ^ 2)
  have hr0 : A.valuation r ≠ 0 := by rw [hr]; exact mul_ne_zero hγ (pow_ne_zero _ hvp0)

  obtain ⟨α₀, hα₀⟩ := exists_valued_coe_sub_lt x ((WithVal.equiv A.valuation).symm r)
    (by rw [WithVal.equiv_symm_apply, WithVal.valued_toVal]; exact hr0)
  set α : ℚbar := WithVal.equiv A.valuation α₀ with hαdef
  have hα₀α : (α₀ : C) = ((α : ℚbar) : C) := by
    rw [hαdef]; simp
  have hα : Valued.v (((α : ℚbar) : C) - x) < γ * A.valuation (p : ℚbar) ^ 2 := by
    rw [← hα₀α, ← hr]
    have : Valued.v (((WithVal.equiv A.valuation).symm r : WithVal A.valuation)) = A.valuation r := by
      rw [WithVal.equiv_symm_apply, WithVal.valued_toVal]
    rw [← this]; exact hα₀
  set δ : A.ValueGroup := Valued.v (((α : ℚbar) : C) - x) with hδ

  have hconj : ∀ σ : ℚbar ≃ₐ[ℚ] ℚbar, σ ∈ L.fixingSubgroup → A.valuation (σ α - α) ≤ δ := by
    intro σ hσ
    obtain ⟨τ, hτ, hτα⟩ := hG1 σ hσ α
    obtain ⟨τ₀, hτ₀H, rfl⟩ := Subgroup.mem_map.mp hτ
    rw [← hτα, ← valued_coe A, ← ι_apply, map_sub, ι_apply, ι_apply]
    change Valued.v ((((τ₀ : ℚbar ≃ₐ[ℚ] ℚbar) α : ℚbar) : C) - ((α : ℚbar) : C)) ≤ δ
    rw [← ValuationSubring.smul_completion_coe]
    have hsplit : τ₀ • ((α : ℚbar) : C) - ((α : ℚbar) : C) =
        τ₀ • (((α : ℚbar) : C) - x) + (x - ((α : ℚbar) : C)) := by
      rw [smul_sub, hx τ₀ hτ₀H]; abel
    rw [hsplit]
    refine (Valued.v.map_add _ _).trans (max_le ?_ ?_)
    · rw [ValuationSubring.valuation_smul_completion]
    · rw [Valuation.map_sub_swap]

  obtain ⟨a, haL, ha⟩ :=
    AXV.exists_mem_map_pow_mul_sub_le A.valuation p hp hvp1 L hiso α δ hconj
  refine ⟨((a : ℚbar) : C), ⟨a, haL, rfl⟩, ?_⟩
  have hvp2 : 0 < A.valuation (p : ℚbar) ^ 2 := pow_pos (zero_lt_iff.mpr hvp0) 2
  have h1 : A.valuation (α - a) < γ := by
    have h2 : A.valuation ((p : ℚbar) ^ 2 * (α - a)) < γ * A.valuation (p : ℚbar) ^ 2 := ha.trans_lt hα
    rw [map_mul, map_pow, mul_comm] at h2
    exact (mul_lt_mul_iff_of_pos_right hvp2).mp h2
  have h3 : δ < γ := by
    refine hα.trans_le ?_
    calc γ * A.valuation (p : ℚbar) ^ 2 ≤ γ * 1 := mul_le_mul_right (pow_le_one' hvp1.le 2) _
      _ = γ := mul_one γ
  have h4 : Valued.v (((a : ℚbar) : C) - ((α : ℚbar) : C)) < γ := by
    rw [← ι_apply, ← ι_apply, ← map_sub, ι_apply, valued_coe, Valuation.map_sub_swap]
    exact h1
  calc Valued.v (((a : ℚbar) : C) - x)
      = Valued.v ((((a : ℚbar) : C) - ((α : ℚbar) : C)) + (((α : ℚbar) : C) - x)) := by
        rw [sub_add_sub_cancel]
    _ ≤ max (Valued.v (((a : ℚbar) : C) - ((α : ℚbar) : C))) (Valued.v (((α : ℚbar) : C) - x)) :=
        Valued.v.map_add _ _
    _ < γ := max_lt h4 h3

end ASTA
p2m_reactivate "P2MW.S_ValuationSubring_forall_smul_completion_eq_self_iff_mem_closure.AXV"

theorem solution
    (p : ℕ) (hp : p.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (H : Subgroup ↥(A.decompositionSubgroup ℚ)) (x : A.valuation.Completion) :
    (∀ σ : ↥(A.decompositionSubgroup ℚ), σ ∈ H → σ • x = x) ↔
      x ∈ closure (((↑) : AlgebraicClosure ℚ → A.valuation.Completion) ''
        (IntermediateField.fixedField (H.map (A.decompositionSubgroup ℚ).subtype) :
          Set (AlgebraicClosure ℚ))) :=
  ⟨ASTA.mem_closure_of_forall_smul_eq_self A H p hp hA x,
    fun hx σ hσ => ASTA.smul_eq_self_of_mem_closure A H x hx σ hσ⟩

end S_ValuationSubring_forall_smul_completion_eq_self_iff_mem_closure
end P2MW
export P2MW.S_ValuationSubring_forall_smul_completion_eq_self_iff_mem_closure (solution)
