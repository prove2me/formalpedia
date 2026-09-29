-- Prove2me | solution 1 for PadicAlgCl.exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3550ceb3-5ede-55e6-9def-19d09e92e501

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open Polynomial

namespace AXL

variable (p : ℕ) [hp : Fact p.Prime]

local notation "Ω" => PadicAlgCl p
local notation "Γ" => (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)

lemma norm_algEquiv (σ : Γ) (x : Ω) : ‖σ x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv σ x).symm

lemma norm_natCast (N : ℕ) : ‖(N : Ω)‖ = ‖(N : ℚ_[p])‖ := by
  rw [← map_natCast (algebraMap ℚ_[p] Ω), PadicAlgCl.norm_extends]

lemma norm_natCast_eq_one {N : ℕ} (h : ¬ p ∣ N) : ‖(N : Ω)‖ = 1 := by
  rw [norm_natCast, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hp.out).mpr h

lemma inv_p_le_norm_natCast {N : ℕ} (hN : N ≠ 0) (h : ¬ p ^ 2 ∣ N) : (p : ℝ)⁻¹ ≤ ‖(N : Ω)‖ := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  by_cases hd : p ∣ N
  · obtain ⟨u, rfl⟩ := hd
    have hu : ¬ p ∣ u := by
      rintro ⟨v, rfl⟩
      exact h ⟨v, by ring⟩
    rw [Nat.cast_mul, norm_mul, norm_natCast_eq_one p hu, mul_one, norm_natCast, Padic.norm_p]
  · rw [norm_natCast_eq_one p hd]
    exact inv_le_one_of_one_le₀ hp1

lemma norm_natCast_pos {N : ℕ} (hN : N ≠ 0) : 0 < ‖(N : Ω)‖ := by
  rw [norm_pos_iff]
  exact_mod_cast hN

lemma norm_multiset_sum_le (t : Multiset Ω) (B : ℝ) (hB : 0 ≤ B) (h : ∀ x ∈ t, ‖x‖ ≤ B) :
    ‖t.sum‖ ≤ B := by
  induction t using Multiset.induction with
  | empty => simpa using hB
  | cons a t ih =>
    rw [Multiset.sum_cons]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · exact h a (Multiset.mem_cons_self a t)
    · exact ih fun x hx => h x (Multiset.mem_cons_of_mem hx)

lemma norm_multiset_prod_le (t : Multiset Ω) (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ x ∈ t, ‖x‖ ≤ δ) :
    ‖t.prod‖ ≤ δ ^ t.card := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, norm_mul, pow_succ, mul_comm (δ ^ _)]
    refine mul_le_mul (h a (Multiset.mem_cons_self a t)) (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))
      (norm_nonneg _) hδ

lemma norm_multiset_prod_eq (t : Multiset Ω) : ‖t.prod‖ = (t.map fun x => ‖x‖).prod := by
  induction t using Multiset.induction with
  | empty => simp
  | cons a t ih => rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, ih]

lemma norm_esymm_le (s : Multiset Ω) (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ x ∈ s, ‖x‖ ≤ δ) (m : ℕ) :
    ‖s.esymm m‖ ≤ δ ^ m := by
  unfold Multiset.esymm
  refine norm_multiset_sum_le p _ _ (pow_nonneg hδ m) ?_
  intro x hx
  rw [Multiset.mem_map] at hx
  obtain ⟨u, hu, rfl⟩ := hx
  rw [Multiset.mem_powersetCard] at hu
  rw [← hu.2]
  exact norm_multiset_prod_le p u δ hδ fun y hy => h y (Multiset.mem_of_le hu.1 hy)

lemma pow_card_le_prod_of_le (t : Multiset ℝ) (a : ℝ) (ha : 0 ≤ a) (h : ∀ x ∈ t, a ≤ x) :
    a ^ t.card ≤ t.prod := by
  induction t using Multiset.induction with
  | empty => simp
  | cons b t ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_comm]
    have hb := h b (Multiset.mem_cons_self b t)
    refine mul_le_mul hb (ih fun x hx => h x (Multiset.mem_cons_of_mem hx)) (pow_nonneg ha _)
      (ha.trans hb)

lemma taylor_multiset_prod (r : Ω) (t : Multiset (Polynomial (PadicAlgCl p))) :
    taylor r t.prod = (t.map fun q => taylor r q).prod := by
  induction t using Multiset.induction with
  | empty => simp [taylor_one]
  | cons a t ih => rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons, taylor_mul, ih]

lemma taylor_prod_X_sub_C (r : Ω) (s : Multiset Ω) :
    taylor r ((s.map fun a => X - C a).prod) = ((s.map fun a => a - r).map fun a => X - C a).prod := by
  rw [taylor_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun a _ => ?_
  simp only [Function.comp_apply, map_sub, taylor_X, taylor_C, C_sub]
  ring

lemma hasseDeriv_map {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (k : ℕ)
    (f : R[X]) : hasseDeriv k (f.map φ) = (hasseDeriv k f).map φ := by
  ext n
  simp [hasseDeriv_coeff, coeff_map]

theorem key (f : (Polynomial (PadicAlgCl p))) (hf : f.Monic) (α : Ω) (δ : ℝ) (hδ : 0 ≤ δ)
    (hroots : ∀ β ∈ f.roots, ‖β - α‖ ≤ δ) (j : ℕ) (hj : j < f.natDegree)
    (hN : (f.natDegree.choose j : Ω) ≠ 0) :
    ∃ β ∈ (hasseDeriv j f).roots,
      ‖β - α‖ ^ (f.natDegree - j) ≤ δ ^ (f.natDegree - j) / ‖(f.natDegree.choose j : Ω)‖ := by
  classical
  set n := f.natDegree with hn
  set m := n - j with hm
  have hm0 : m ≠ 0 := by omega
  have hmj : m + j = n := by omega

  have hsplit : f = (f.roots.map fun a => X - C a).prod :=
    (IsAlgClosed.splits f).eq_prod_roots_of_monic hf
  have hcard : f.roots.card = n := ((IsAlgClosed.splits f).natDegree_eq_card_roots).symm
  set s : Multiset (PadicAlgCl p) := f.roots.map fun a => a - α with hs
  have hscard : s.card = n := by rw [hs, Multiset.card_map, hcard]
  have hsδ : ∀ x ∈ s, ‖x‖ ≤ δ := by
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
  have heval_le : ‖g.eval α‖ ≤ δ ^ m := by
    rw [hg, ← taylor_coeff, hcoeff, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, ← hm]
    exact norm_esymm_le p s δ hδ hsδ m

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
  have hnormprod : ‖(n.choose j : Ω)‖ * (g.roots.map fun β => ‖α - β‖).prod ≤ δ ^ m := by
    have := heval_le
    rw [hevalprod, norm_mul, norm_multiset_prod_eq, Multiset.map_map] at this
    exact this

  have hne : g.roots.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty, ← Multiset.card_pos, hgcard]
    exact Nat.pos_of_ne_zero hm0
  obtain ⟨β₀, hβ₀, hmin⟩ := Finset.exists_min_image g.roots.toFinset (fun β => ‖α - β‖) hne
  rw [Multiset.mem_toFinset] at hβ₀
  refine ⟨β₀, hβ₀, ?_⟩
  have hNpos : 0 < ‖(n.choose j : Ω)‖ := norm_pos_iff.mpr hN
  have hpow : ‖α - β₀‖ ^ m ≤ (g.roots.map fun β => ‖α - β‖).prod := by
    have := pow_card_le_prod_of_le (g.roots.map fun β => ‖α - β‖) ‖α - β₀‖ (norm_nonneg _)
      (by
        intro x hx
        rw [Multiset.mem_map] at hx
        obtain ⟨β, hβ, rfl⟩ := hx
        exact hmin β (Multiset.mem_toFinset.mpr hβ))
    rwa [Multiset.card_map, hgcard] at this
  rw [norm_sub_rev, le_div_iff₀ hNpos, mul_comm]
  exact (mul_le_mul_of_nonneg_left hpow hNpos.le).trans hnormprod

section Galois

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

scoped instance isAlgClosureK : IsAlgClosure K Ω :=
  ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) K⟩

scoped instance normalK : Normal K Ω := IsAlgClosure.normal K Ω

lemma isIntegralK (α : Ω) : IsIntegral K α :=
  (Algebra.IsAlgebraic.isAlgebraic (R := K) α).isIntegral

lemma roots_minpoly_norm_sub_le (α : Ω) (δ : ℝ)
    (h : ∀ σ : Γ, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) :
    ∀ β ∈ ((minpoly K α).map (algebraMap K Ω)).roots, ‖β - α‖ ≤ δ := by
  intro β hβ
  have hint := isIntegralK p K α
  have hmon : ((minpoly K α).map (algebraMap K Ω)).Monic := (minpoly.monic hint).map _
  rw [mem_roots hmon.ne_zero, IsRoot.def, eval_map, ← aeval_def] at hβ
  have hmin : minpoly K α = minpoly K β :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hβ (minpoly.monic hint)
  have horb : β ∈ MulAction.orbit (Ω ≃ₐ[K] Ω) α :=
    (Normal.minpoly_eq_iff_mem_orbit Ω).mp hmin.symm
  obtain ⟨τ, hτ⟩ := horb
  set σ : Γ := τ.restrictScalars ℚ_[p] with hσ
  have hσK : σ ∈ K.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change τ x = x
    exact τ.commutes ⟨x, hx⟩
  have hσα : σ α = β := hτ
  rw [← hσα]
  exact h σ hσK

lemma natDegree_minpoly_le_of_mem_roots_hasseDeriv (α : Ω) (j : ℕ)
    (hj : j < (minpoly K α).natDegree)
    (β : Ω) (hβ : β ∈ (hasseDeriv j ((minpoly K α).map (algebraMap K Ω))).roots) :
    (minpoly K β).natDegree ≤ (minpoly K α).natDegree - j := by
  set gK := hasseDeriv j (minpoly K α) with hgK
  have hmap : hasseDeriv j ((minpoly K α).map (algebraMap K Ω)) = gK.map (algebraMap K Ω) :=
    hasseDeriv_map _ _ _
  have hint := isIntegralK p K α

  have hcoeff : gK.coeff ((minpoly K α).natDegree - j) = ((minpoly K α).natDegree.choose j : K) := by
    rw [hgK, hasseDeriv_coeff, Nat.sub_add_cancel hj.le, (minpoly.monic hint).coeff_natDegree, mul_one]
  have hgK0 : gK ≠ 0 := by
    intro h0
    have := hcoeff
    rw [h0, coeff_zero] at this
    have hc : ((minpoly K α).natDegree.choose j : K) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hj.le).ne'
    exact hc this.symm
  have hmap0 : gK.map (algebraMap K Ω) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero]
  rw [hmap, mem_roots hmap0, IsRoot.def, eval_map, ← aeval_def] at hβ
  have hdeg := minpoly.degree_le_of_ne_zero K β hgK0 hβ
  refine (natDegree_le_natDegree hdeg).trans ?_
  rw [hgK]
  exact natDegree_hasseDeriv_le _ _

lemma norm_conj_sub_le (α β : Ω) (δ ε : ℝ)
    (h : ∀ σ : Γ, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) (hβ : ‖β - α‖ ≤ ε) (hδε : δ ≤ ε) :
    ∀ σ : Γ, σ ∈ K.fixingSubgroup → ‖σ β - β‖ ≤ ε := by
  intro σ hσ
  have hsplit : σ β - β = σ (β - α) + ((σ α - α) + (α - β)) := by
    rw [map_sub]; abel
  rw [hsplit]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_algEquiv]; exact hβ
  · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((h σ hσ).trans hδε) ?_)
    rw [norm_sub_rev]; exact hβ

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
  have h0 : n.choose (p ^ L) % p = 0 := Nat.eq_zero_of_dvd_of_lt hd |> fun _ => Nat.mod_eq_zero_of_dvd hd
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

noncomputable def E (n : ℕ) : ℝ := ∑ i ∈ Finset.range (Nat.log p n), ((p : ℝ)⁻¹) ^ i

noncomputable def B (n : ℕ) : ℝ := (p : ℝ) ^ (E p n)

lemma one_le_p : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le

lemma p_pos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos

lemma E_nonneg (n : ℕ) : 0 ≤ E p n :=
  Finset.sum_nonneg fun i _ => pow_nonneg (inv_nonneg.mpr (p_pos p).le) i

lemma E_mono {m n : ℕ} (h : m ≤ n) : E p m ≤ E p n := by
  unfold E
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.log_mono_right h)) ?_
  intro i _ _
  exact pow_nonneg (inv_nonneg.mpr (p_pos p).le) i

lemma E_le_two (n : ℕ) : E p n ≤ 2 := by
  unfold E
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_geometric_two_le (Nat.log p n))
  rw [one_div]
  refine pow_le_pow_left₀ (inv_nonneg.mpr (p_pos p).le) ?_ i
  refine inv_anti₀ (by norm_num) ?_
  exact_mod_cast hp.out.two_le

lemma E_pow_succ (L : ℕ) : E p (p ^ (L + 1)) = E p (p ^ L) + ((p : ℝ)⁻¹) ^ L := by
  unfold E
  rw [Nat.log_pow hp.out.one_lt, Nat.log_pow hp.out.one_lt, Finset.sum_range_succ]

lemma one_le_B (n : ℕ) : 1 ≤ B p n := Real.one_le_rpow (one_le_p p) (E_nonneg p n)

lemma B_pos (n : ℕ) : 0 < B p n := lt_of_lt_of_le one_pos (one_le_B p n)

lemma B_mono {m n : ℕ} (h : m ≤ n) : B p m ≤ B p n :=
  Real.rpow_le_rpow_of_exponent_le (one_le_p p) (E_mono p h)

lemma B_le_sq (n : ℕ) : B p n ≤ (p : ℝ) ^ 2 := by
  have := Real.rpow_le_rpow_of_exponent_le (one_le_p p) (E_le_two p n)
  rw [B]
  refine this.trans_eq ?_
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

lemma B_pow_succ (L : ℕ) : B p (p ^ (L + 1)) = B p (p ^ L) * (p : ℝ) ^ (((p : ℝ)⁻¹) ^ L) := by
  rw [B, E_pow_succ, Real.rpow_add (p_pos p), B]

theorem main (n : ℕ) : ∀ (K : IntermediateField ℚ_[p] Ω) (α : Ω) (δ : ℝ),
    (minpoly K α).natDegree ≤ n →
    (∀ σ : Γ, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) →
      ∃ a ∈ K, ‖α - a‖ ≤ B p n * δ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K α δ hdeg hconj
    have hδ : 0 ≤ δ := by
      have := hconj 1 (Subgroup.one_mem _)
      simpa using this
    have hint := isIntegralK p K α
    set n₀ := (minpoly K α).natDegree with hn₀
    have hn₀pos : 0 < n₀ := minpoly.natDegree_pos hint

    by_cases h1 : n₀ = 1
    · have hα : α ∈ (algebraMap K Ω).range := minpoly.natDegree_eq_one_iff.mp h1
      obtain ⟨a, ha⟩ := hα
      refine ⟨(a : Ω), a.2, ?_⟩
      have : (a : Ω) = α := ha
      rw [this, sub_self, norm_zero]
      exact mul_nonneg (B_pos p n).le hδ
    have hn₀2 : 2 ≤ n₀ := by omega

    set L := Nat.log p n₀ with hL
    have hpL : p ^ L ≤ n₀ := Nat.pow_log_le_self p (by omega)
    have hn₀lt : n₀ < p ^ (L + 1) := Nat.lt_pow_succ_log_self hp.out.one_lt n₀

    set f : (Polynomial (PadicAlgCl p)) := (minpoly K α).map (algebraMap K Ω) with hf
    have hfmon : f.Monic := (minpoly.monic hint).map _
    have hfdeg : f.natDegree = n₀ := (minpoly.monic hint).natDegree_map _
    have hroots : ∀ β ∈ f.roots, ‖β - α‖ ≤ δ := roots_minpoly_norm_sub_le p K α δ hconj

    have cont : ∀ (m : ℕ) (Λ : ℝ), 0 < m → m < n₀ → 1 ≤ Λ →
        (n₀.choose (n₀ - m) : Ω) ≠ 0 →
        (‖(n₀.choose (n₀ - m) : Ω)‖)⁻¹ ≤ Λ ^ m →
        B p m * Λ ≤ B p n₀ →
        ∃ a ∈ K, ‖α - a‖ ≤ B p n * δ := by
      intro m Λ hm0 hmn hΛ1 hN hNΛ hBΛ
      set j := n₀ - m with hj
      have hjlt : j < f.natDegree := by rw [hfdeg]; omega
      have hmj : f.natDegree - j = m := by rw [hfdeg]; omega
      have hNf : (f.natDegree.choose j : Ω) ≠ 0 := by rw [hfdeg]; exact hN
      obtain ⟨β, hβ, hβle⟩ := key p f hfmon α δ hδ hroots j hjlt hNf
      rw [hmj, hfdeg] at hβle

      have hβΛ : ‖β - α‖ ≤ Λ * δ := by
        have hΛδ : 0 ≤ Λ * δ := mul_nonneg (zero_le_one.trans hΛ1) hδ
        refine le_of_pow_le_pow_left₀ hm0.ne' hΛδ ?_
        refine hβle.trans ?_
        rw [div_eq_mul_inv, mul_pow, mul_comm]
        exact mul_le_mul_of_nonneg_right hNΛ (pow_nonneg hδ m)

      have hβdeg : (minpoly K β).natDegree ≤ m := by
        have := natDegree_minpoly_le_of_mem_roots_hasseDeriv p K α j (by omega) β
          (by rw [← hf]; exact hβ)
        omega

      have hβconj := norm_conj_sub_le p K α β δ (Λ * δ) hconj hβΛ
        (by nlinarith [hδ, hΛ1])

      have hmn' : m < n := lt_of_lt_of_le hmn hdeg
      obtain ⟨a, haK, ha⟩ := ih m hmn' K β (Λ * δ) hβdeg hβconj
      refine ⟨a, haK, ?_⟩
      have hsplit : α - a = (α - β) + (β - a) := by abel
      rw [hsplit]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_sub_rev]
        refine hβΛ.trans ?_
        have : Λ ≤ B p n := by
          have h1 : Λ ≤ B p m * Λ := le_mul_of_one_le_left (zero_le_one.trans hΛ1) (one_le_B p m)
          exact h1.trans (hBΛ.trans (B_mono p hdeg))
        exact mul_le_mul_of_nonneg_right this hδ
      · refine ha.trans ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hBΛ.trans (B_mono p hdeg)) hδ
    by_cases hcase : p ^ L < n₀
    ·
      refine cont (p ^ L) 1 (pow_pos hp.out.pos L) hcase le_rfl ?_ ?_ ?_
      · rw [Nat.choose_symm hpL]
        have h := not_dvd_choose_prime_pow p hpL hn₀lt
        intro h0
        have h1 : ‖((n₀.choose (p ^ L) : ℕ) : Ω)‖ = 1 := norm_natCast_eq_one p h
        rw [h0, norm_zero] at h1
        exact zero_ne_one h1
      · rw [Nat.choose_symm hpL, norm_natCast_eq_one p (not_dvd_choose_prime_pow p hpL hn₀lt),
          inv_one, one_pow]
      · rw [mul_one]; exact B_mono p hpL
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
      set Λ : ℝ := (p : ℝ) ^ ((m : ℝ)⁻¹) with hΛ
      have hΛ1 : 1 ≤ Λ := Real.one_le_rpow (one_le_p p) (by positivity)
      refine cont m Λ hm0 hmn hΛ1 ?_ ?_ ?_
      · rw [Nat.choose_symm hmle]
        exact_mod_cast hNne
      · rw [Nat.choose_symm hmle]
        have hle := inv_p_le_norm_natCast p hNne hNnat
        have hΛm : Λ ^ m = p := by
          rw [hΛ]; exact Real.rpow_inv_natCast_pow (p_pos p).le hm0.ne'
        rw [hΛm]
        rw [inv_le_comm₀ (norm_natCast_pos p hNne) (p_pos p)]
        exact hle
      ·
        have hL' : L = (L - 1) + 1 := by omega
        have hΛ' : Λ = (p : ℝ) ^ (((p : ℝ)⁻¹) ^ (L - 1)) := by
          rw [hΛ, hm]
          congr 1
          rw [Nat.cast_pow, ← inv_pow]
        rw [hn₀eq, hL', B_pow_succ, hΛ']

end AXL
p2m_reactivate "P2MW.S_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le.AXL"

theorem solution (p : ℕ) [Fact p.Prime] :
    ∃ c : ℝ, 0 < c ∧
      ∀ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (α : PadicAlgCl p) (δ : ℝ),
        (∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ K.fixingSubgroup → ‖σ α - α‖ ≤ δ) →
          ∃ a ∈ K, ‖α - a‖ ≤ c * δ := by
  refine ⟨(p : ℝ) ^ 2, pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) 2, ?_⟩
  intro K α δ h
  have hδ : 0 ≤ δ := by
    have := h 1 (Subgroup.one_mem _)
    simpa using this
  obtain ⟨a, haK, ha⟩ := AXL.main p ((minpoly K α).natDegree) K α δ le_rfl h
  exact ⟨a, haK, ha.trans (mul_le_mul_of_nonneg_right (AXL.B_le_sq p _) hδ)⟩

end S_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le
end P2MW
export P2MW.S_PadicAlgCl_exists_mem_intermediateField_norm_sub_le_mul_of_forall_norm_algEquiv_sub_le (solution)
