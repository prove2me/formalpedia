-- Prove2me | solution 1 for RSSubspaceDesign.lemma_2_20
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T22:52:40.353591+00:00
-- url     : https://prove2.me/submissions/146d0b0e-5e9d-4943-9ded-d6daaf0f34a9

import Mathlib
import Definitions.Def_RSSubspaceDesign_ratFuncAlgebra
import Definitions.Def_RSSubspaceDesign_IsConjugateSet

open Polynomial RSSubspaceDesign

set_option linter.style.haveILetI false

section L220_group

theorem L220_comm {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F]
    (a b : F ≃ₐ[K] F) : a * b = b * a := by
  have : Finite K := Finite.of_injective _ (algebraMap K F).injective
  obtain ⟨p, _⟩ := CharP.exists K
  haveI := Fact.mk (CharP.char_is_prime K p)
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow K p F a
  obtain ⟨j, hj⟩ := FiniteField.exists_forall_apply_eq_pow K p F b
  ext x
  simp only [AlgEquiv.mul_apply, hi, hj, ← pow_mul, mul_comm]

noncomputable def L220_tau {G : Type*} [Monoid G] {g : ℕ} (σ : Fin g → G) (ω : Fin g → ℕ) : G :=
  (List.ofFn fun j => σ j ^ ω j).prod

theorem L220_tau_add {G : Type*} [Monoid G] (hc : ∀ a b : G, a * b = b * a) {g : ℕ}
    (σ : Fin g → G) (ω ν : Fin g → ℕ) :
    L220_tau σ (ω + ν) = L220_tau σ ω * L220_tau σ ν := by
  letI : CommMonoid G := { ‹Monoid G› with mul_comm := hc }
  simp only [L220_tau, List.prod_ofFn, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

theorem L220_tau_zero {G : Type*} [Monoid G] {g : ℕ} (σ : Fin g → G) :
    L220_tau σ 0 = 1 := by
  simp [L220_tau]

theorem L220_tau_smul {G : Type*} [Monoid G] (hc : ∀ a b : G, a * b = b * a) {g : ℕ}
    (σ : Fin g → G) (ω : Fin g → ℕ) (m : ℕ) :
    L220_tau σ (m • ω) = L220_tau σ ω ^ m := by
  induction m with
  | zero => simp [L220_tau_zero]
  | succ m ih => rw [succ_nsmul, L220_tau_add hc, ih, pow_succ]

theorem L220_tau_single {G : Type*} [Monoid G] (hc : ∀ a b : G, a * b = b * a) {g : ℕ}
    (σ : Fin g → G) (j : Fin g) : L220_tau σ (Pi.single j 1) = σ j := by
  letI : CommMonoid G := { ‹Monoid G› with mul_comm := hc }
  simp only [L220_tau, List.prod_ofFn]
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem L220_tau_surj {G : Type*} [Group G] [Finite G] (hc : ∀ a b : G, a * b = b * a) {g : ℕ}
    (σ : Fin g → G) (hσ : Subgroup.closure (Set.range σ) = ⊤) (x : G) :
    ∃ ω, L220_tau σ ω = x := by
  have hx : x ∈ Subgroup.closure (Set.range σ) := by rw [hσ]; trivial
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact ⟨Pi.single j 1, L220_tau_single hc σ j⟩
  | one => exact ⟨0, L220_tau_zero σ⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, L220_tau_add hc σ a b⟩
  | inv y _ hy =>
    obtain ⟨a, rfl⟩ := hy
    refine ⟨(orderOf (L220_tau σ a) - 1) • a, ?_⟩
    rw [L220_tau_smul hc]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos _), pow_orderOf_eq_one]

end L220_group

section L220_trace

theorem L220_ratFunc_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F] (t : K[X]) :
    (letI := ratFuncAlgebra K F
     algebraMap (RatFunc K) (RatFunc F) (algebraMap K[X] (RatFunc K) t)) =
      algebraMap F[X] (RatFunc F) (t.map (algebraMap K F)) := by
  letI := ratFuncAlgebra K F
  have h1 : algebraMap K[X] (RatFunc K) t =
      algebraMap K[X] (RatFunc K) t / algebraMap K[X] (RatFunc K) 1 := by simp
  show RatFunc.mapRingHom _ _ (algebraMap K[X] (RatFunc K) t) = _
  rw [h1, RatFunc.coe_mapRingHom_eq_coe_map, RatFunc.map_apply_div]
  simp

noncomputable def L220_T {K F : Type*} [Field K] [Field F] [Algebra K F] (q : F[X]) : K[X] :=
  ∑ n ∈ q.support, monomial n (Algebra.trace K F (q.coeff n))

theorem L220_T_coeff {K F : Type*} [Field K] [Field F] [Algebra K F] (q : F[X]) (m : ℕ) :
    (L220_T (K := K) q).coeff m = Algebra.trace K F (q.coeff m) := by
  classical
  simp only [L220_T, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single m]
  · simp
  · intro b _ hb; simp [hb]
  · intro hm; simp [notMem_support_iff.mp hm]

theorem L220_sum_aut {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F] (q : F[X]) :
    ∑ τ : F ≃ₐ[K] F, q.map τ.toRingEquiv.toRingHom = (L220_T (K := K) q).map (algebraMap K F) := by
  have : Finite K := Finite.of_injective _ (algebraMap K F).injective
  have := Fintype.ofFinite F
  have := Fintype.ofFinite K
  ext n
  rw [finsetSum_coeff, coeff_map, L220_T_coeff, trace_eq_sum_automorphisms]
  simp [coeff_map]

theorem L220_poly_indep {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F] {d : ℕ}
    (u : Fin d → F[X])
    (hu : letI := ratFuncAlgebra K F
      LinearIndependent (RatFunc K) fun a => algebraMap F[X] (RatFunc F) (u a))
    (p : Fin d → F[X])
    (hp : ∀ τ : F ≃ₐ[K] F, ∑ a, (u a).map τ.toRingEquiv.toRingHom * p a = 0) : p = 0 := by
  letI := ratFuncAlgebra K F
  have : Finite K := Finite.of_injective _ (algebraMap K F).injective
  have := Fintype.ofFinite F
  have := Fintype.ofFinite K
  -- step 1
  have h1 : ∀ τ : F ≃ₐ[K] F, ∑ a, u a * (p a).map τ.toRingEquiv.toRingHom = 0 := by
    intro τ
    have := congrArg (Polynomial.map τ.toRingEquiv.toRingHom) (hp τ.symm)
    rw [Polynomial.map_zero, Polynomial.map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_map]
    congr 1
    ext n; simp [coeff_map]
  -- step 2
  have h2 : ∀ l : F, ∑ a, u a * (L220_T (K := K) (C l * p a)).map (algebraMap K F) = 0 := by
    intro l
    simp_rw [← L220_sum_aut, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun τ _ => ?_
    have : ∀ a, u a * (C l * p a).map τ.toRingEquiv.toRingHom =
        C (τ l) * (u a * (p a).map τ.toRingEquiv.toRingHom) := by
      intro a; rw [Polynomial.map_mul, map_C, mul_left_comm]; rfl
    simp_rw [this, ← Finset.mul_sum, h1 τ, mul_zero]
  -- step 3
  have h3 : ∀ l : F, ∀ a, L220_T (K := K) (C l * p a) = 0 := by
    intro l
    have hli := (linearIndependent_iff'.mp hu) Finset.univ
      (fun a => algebraMap K[X] (RatFunc K) (L220_T (K := K) (C l * p a)))
    intro a
    have := hli ?_ a (Finset.mem_univ a)
    · exact (IsFractionRing.injective K[X] (RatFunc K)) (by simpa using this)
    · simp only [Algebra.smul_def, L220_ratFunc_algebraMap, ← map_mul, ← map_sum]
      simp_rw [mul_comm _ (u _)]
      rw [h2 l, map_zero]
  -- step 4
  funext a
  ext n
  have hnd := traceForm_nondegenerate K F
  simp only [Pi.zero_apply, coeff_zero]
  apply hnd.1
  intro l
  have := congrArg (fun q => q.coeff n) (h3 l a)
  simp only [L220_T_coeff, coeff_C_mul, coeff_zero] at this
  simpa [Algebra.traceForm_apply, mul_comm] using this


noncomputable def L220_row {K F : Type*} [Field K] [Field F] [Algebra K F] {d : ℕ}
    (u : Fin d → F[X]) (τ : F ≃ₐ[K] F) : Fin d → RatFunc F :=
  fun a => algebraMap F[X] (RatFunc F) ((u a).map τ.toRingEquiv.toRingHom)

theorem L220_span_top {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F] {d : ℕ}
    (u : Fin d → F[X])
    (hu : letI := ratFuncAlgebra K F
      LinearIndependent (RatFunc K) fun a => algebraMap F[X] (RatFunc F) (u a)) :
    Submodule.span (RatFunc F) (Set.range (L220_row (K := K) u)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hle⟩ :=
    Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  set c : Fin d → RatFunc F := fun a => f (Pi.single a 1) with hc
  have hf : ∀ v, f v = ∑ a, v a * c a := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ f v]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_eq_mul]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors F[X])
    (Finset.univ : Finset (Fin d)) c
  choose p hp using fun a => hb a (Finset.mem_univ a)
  have hb0 : algebraMap F[X] (RatFunc F) (b : F[X]) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hP : p = 0 := by
    apply L220_poly_indep u hu p
    intro τ
    apply IsFractionRing.injective F[X] (RatFunc F)
    have h0 : f (L220_row u τ) = 0 := hle (Submodule.subset_span ⟨τ, rfl⟩)
    rw [hf] at h0
    rw [map_zero, map_sum]
    simp_rw [map_mul, hp, Algebra.smul_def]
    calc ∑ a, algebraMap F[X] (RatFunc F) ((u a).map τ.toRingEquiv.toRingHom) *
          (algebraMap F[X] (RatFunc F) b * c a)
        = algebraMap F[X] (RatFunc F) b * ∑ a, L220_row u τ a * c a := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [L220_row]; ring
      _ = 0 := by rw [h0, mul_zero]
  apply hf0
  refine LinearMap.ext fun v => ?_
  rw [hf, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun a _ => ?_
  have := hp a
  rw [hP, Pi.zero_apply, map_zero, Algebra.smul_def] at this
  rcases mul_eq_zero.mp this.symm with h | h
  · exact absurd h hb0
  · rw [h, mul_zero]

end L220_trace

section L220_greedy

theorem L220_lin_finite {R : Type*} [Field R] {g d : ℕ} (r : (Fin g → ℕ) → (Fin d → R))
    (S : Set (Fin g → ℕ))
    (hS : ∀ ω ∈ S, r ω ∉ Submodule.span R (r '' {μ | toLex μ < toLex ω}))
    (t : Finset (Fin g → ℕ)) (ht : (t : Set (Fin g → ℕ)) ⊆ S) :
    LinearIndepOn R r (t : Set (Fin g → ℕ)) := by
  classical
  revert ht
  refine Finset.induction_on_max_value (fun ω => toLex ω) t (by simp) ?_
  intro a s has hmax ih ht
  rw [Finset.coe_insert, linearIndepOn_insert (by simpa using has)]
  refine ⟨ih (fun x hx => ht (by simp [hx])), fun hmem => ?_⟩
  apply hS a (ht (by simp))
  refine Submodule.span_mono (Set.image_mono ?_) hmem
  intro x hx
  have h1 := hmax x hx
  have h2 : x ≠ a := fun h => has (h ▸ hx)
  exact lt_of_le_of_ne h1 (fun h => h2 (toLex.injective h))

theorem L220_greedy {R : Type*} [Field R] {g d : ℕ} (r : (Fin g → ℕ) → (Fin d → R))
    (htop : Submodule.span R (Set.range r) = ⊤)
    (hshift : ∀ (ν δ : Fin g → ℕ) (T : Set (Fin g → ℕ)), r ν ∈ Submodule.span R (r '' T) →
      r (ν + δ) ∈ Submodule.span R (r '' ((· + δ) '' T))) :
    ∃ B : Finset (Fin g → ℕ), B.card = d ∧ (∀ ω ∈ B, ∀ ν, ν ≤ ω → ν ∈ B) ∧
      LinearIndependent R (fun ω : B => r ω) := by
  classical
  set S : Set (Fin g → ℕ) := {ω | r ω ∉ Submodule.span R (r '' {μ | toLex μ < toLex ω})} with hSdef
  have hS : ∀ ω ∈ S, r ω ∉ Submodule.span R (r '' {μ | toLex μ < toLex ω}) := fun ω h => h
  -- finite subsets of S have card ≤ d
  have hcard : ∀ t : Finset (Fin g → ℕ), (t : Set _) ⊆ S → t.card ≤ d := by
    intro t ht
    have hli := L220_lin_finite r S hS t ht
    have := hli.linearIndependent.fintype_card_le_finrank
    simpa using this
  have hfin : S.Finite := by
    by_contra hinf
    obtain ⟨t, ht, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (d + 1)
    have := hcard t ht
    omega
  set B := hfin.toFinset with hB
  have hBS : (B : Set (Fin g → ℕ)) = S := by simp [hB]
  have hli : LinearIndependent R (fun ω : B => r ω) :=
    (L220_lin_finite r S hS B (by rw [hBS])).linearIndependent
  -- spanning
  have hspan : ∀ ω, r ω ∈ Submodule.span R (r '' S) := by
    intro ω
    induction ω using (InvImage.wf (fun ω : Fin g → ℕ => toLex ω) wellFounded_lt).induction with
    | _ ω ih =>
      by_cases hω : ω ∈ S
      · exact Submodule.subset_span ⟨ω, hω, rfl⟩
      · have : r ω ∈ Submodule.span R (r '' {μ | toLex μ < toLex ω}) := by
          simpa [hSdef] using hω
        refine (Submodule.span_le.mpr ?_) this
        rintro _ ⟨μ, hμ, rfl⟩
        exact ih μ hμ
  have hspanS : Submodule.span R (r '' S) = ⊤ := by
    rw [eq_top_iff, ← htop, Submodule.span_le]
    rintro _ ⟨ω, rfl⟩
    exact hspan ω
  refine ⟨B, ?_, ?_, hli⟩
  · have h1 := finrank_span_eq_card hli
    have h2 : Set.range (fun ω : B => r ω) = r '' S := by
      rw [← hBS]; ext; simp
    rw [h2, hspanS, finrank_top, Module.finrank_fin_fun] at h1
    rw [h1]; simp
  · intro ω hω ν hνω
    have hωS : ω ∈ S := by rw [← hBS]; exact hω
    by_contra hν
    have hνS : ν ∉ S := by rw [← hBS]; exact hν
    have h1 : r ν ∈ Submodule.span R (r '' {μ | toLex μ < toLex ν}) := by
      simpa [hSdef] using hνS
    have h2 := hshift ν (ω - ν) _ h1
    have hων : ν + (ω - ν) = ω := by
      funext j; simp only [Pi.add_apply, Pi.sub_apply]; exact Nat.add_sub_cancel' (hνω j)
    rw [hων] at h2
    apply hS ω hωS
    refine Submodule.span_mono (Set.image_mono ?_) h2
    rintro _ ⟨μ, hμ, rfl⟩
    simp only [Set.mem_ofPred_eq] at hμ ⊢
    calc toLex (μ + (ω - ν)) = toLex μ + toLex (ω - ν) := toLex_add _ _
      _ < toLex ν + toLex (ω - ν) := add_lt_add_left hμ _
      _ = toLex ω := by rw [← toLex_add, hων]

end L220_greedy

section L220_move

theorem L220_supp_card {g d : ℕ} (B : Finset (Fin g → ℕ)) (hcard : B.card = d)
    (hdown : ∀ ω ∈ B, ∀ ν, ν ≤ ω → ν ∈ B) (ω : Fin g → ℕ) (hω : ω ∈ B) :
    2 ^ (Finset.univ.filter fun j => ω j ≠ 0).card ≤ d := by
  classical
  rw [← Finset.card_powerset, ← hcard]
  refine Finset.card_le_card_of_injOn (fun T j => if j ∈ T then 1 else 0) ?_ ?_
  · intro T hT
    simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
      Finset.coe_subset] at hT
    apply hdown ω hω
    intro j
    by_cases hj : j ∈ T
    · have := hT hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
      simp only [hj, if_true]; omega
    · simp [hj]
  · intro T _ T' _ h
    ext j
    have := congrFun h j
    by_cases hj : j ∈ T <;> by_cases hj' : j ∈ T' <;> simp_all

theorem L220_supp_le_logb {g d : ℕ} (B : Finset (Fin g → ℕ)) (hcard : B.card = d) (hd : 1 ≤ d)
    (hdown : ∀ ω ∈ B, ∀ ν, ν ≤ ω → ν ∈ B) (ω : Fin g → ℕ) (hω : ω ∈ B) :
    ((Finset.univ.filter fun j => ω j ≠ 0).card : ℝ) ≤ Real.logb 2 d := by
  have h := L220_supp_card B hcard hdown ω hω
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hd)]
  rw [Real.rpow_natCast]
  exact_mod_cast h

theorem L220_fix {K F : Type*} [Field K] [Field F] [Algebra K F] {g : ℕ}
    (σ : Fin g → (F ≃ₐ[K] F)) (ω : Fin g → ℕ) (x : F)
    (h : ∀ j, ω j ≠ 0 → σ j x = x) :
    (List.ofFn fun j => σ j ^ ω j).prod x = x := by
  have hmem : (List.ofFn fun j => σ j ^ ω j).prod ∈ MulAction.stabilizer (F ≃ₐ[K] F) x := by
    apply Subgroup.list_prod_mem
    intro y hy
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    by_cases hj : ω j = 0
    · simp [hj]
    · apply Subgroup.pow_mem
      rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
      exact h j hj
  rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at hmem
  exact hmem

open Classical in
theorem L220_move {K F : Type*} [Field K] [Field F] [Algebra K F] {g d : ℕ} (hd : 1 ≤ d)
    (σ : Fin g → (F ≃ₐ[K] F)) (B : Finset (Fin g → ℕ)) (hcard : B.card = d)
    (hdown : ∀ ω ∈ B, ∀ ν, ν ≤ ω → ν ∈ B) (n : ℕ) (α : Fin n → F) :
    (∑ i, ((B.filter fun ω => (List.ofFn fun j => σ j ^ ω j).prod (α i) ≠ α i).card : ℝ)) ≤
        d * Real.logb 2 d *
          ((Finset.univ.sup fun j => (Finset.univ.filter fun i => σ j (α i) ≠ α i).card : ℕ) : ℝ) := by
  set Mx : ℕ := Finset.univ.sup fun j => (Finset.univ.filter fun i => σ j (α i) ≠ α i).card
    with hMx
  set supp : (Fin g → ℕ) → Finset (Fin g) := fun ω => Finset.univ.filter fun j => ω j ≠ 0
    with hsupp
  -- pointwise
  have h1 : ∀ i, (B.filter fun ω => (List.ofFn fun j => σ j ^ ω j).prod (α i) ≠ α i).card ≤
      ∑ ω ∈ B, ((supp ω).filter fun j => σ j (α i) ≠ α i).card := by
    intro i
    rw [Finset.card_filter]
    refine Finset.sum_le_sum fun ω _ => ?_
    split_ifs with hmv
    · rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero]
      intro hempty
      apply hmv
      apply L220_fix
      intro j hj
      by_contra hne
      have : j ∈ (supp ω).filter fun j => σ j (α i) ≠ α i := by
        simp [hsupp, hj, hne]
      rw [hempty] at this
      simp at this
    · exact Nat.zero_le _
  have h2 : (∑ i, (B.filter fun ω => (List.ofFn fun j => σ j ^ ω j).prod (α i) ≠ α i).card) ≤
      ∑ ω ∈ B, (supp ω).card * Mx := by
    refine (Finset.sum_le_sum fun i _ => h1 i).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun ω _ => ?_
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    calc ∑ j ∈ supp ω, ∑ i, (if σ j (α i) ≠ α i then 1 else 0)
        ≤ ∑ j ∈ supp ω, Mx := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← Finset.card_filter]
          exact Finset.le_sup (f := fun j => (Finset.univ.filter fun i => σ j (α i) ≠ α i).card)
            (Finset.mem_univ j)
      _ = (supp ω).card * Mx := by rw [Finset.sum_const, smul_eq_mul]
  have h3 : ((∑ i, (B.filter fun ω => (List.ofFn fun j => σ j ^ ω j).prod (α i) ≠ α i).card :
      ℕ) : ℝ) ≤ ∑ ω ∈ B, ((supp ω).card : ℝ) * Mx := by exact_mod_cast h2
  push_cast at h3
  refine h3.trans ?_
  calc ∑ ω ∈ B, ((supp ω).card : ℝ) * Mx ≤ ∑ ω ∈ B, Real.logb 2 d * Mx := by
        refine Finset.sum_le_sum fun ω hω => ?_
        exact mul_le_mul_of_nonneg_right (L220_supp_le_logb B hcard hd hdown ω hω)
          (Nat.cast_nonneg _)
    _ = d * Real.logb 2 d * Mx := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul, mul_assoc]

end L220_move

section L220_shift

theorem L220_span_map {R ι : Type*} [CommRing R] (ψ : R →+* R) (S : Set (ι → R)) (v : ι → R)
    (hv : v ∈ Submodule.span R S) :
    (fun a => ψ (v a)) ∈ Submodule.span R ((fun w a => ψ (w a)) '' S) := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero =>
    convert Submodule.zero_mem (Submodule.span R ((fun w a => ψ (w a)) '' S)) using 1
    funext a; simp
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    convert this using 1
    funext a; simp
  | smul c x _ hx =>
    have := Submodule.smul_mem _ (ψ c) hx
    convert this using 1
    funext a; simp

end L220_shift

section L220_main

theorem L220_row_shift {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F] {g d : ℕ}
    (u : Fin d → F[X]) (σ : Fin g → (F ≃ₐ[K] F)) (μ δ : Fin g → ℕ) :
    (fun a => (IsFractionRing.ringEquivOfRingEquiv (K := RatFunc F) (L := RatFunc F)
      (Polynomial.mapEquiv (L220_tau σ δ).toRingEquiv)) (L220_row u (L220_tau σ μ) a)) =
      L220_row u (L220_tau σ (μ + δ)) := by
  funext a
  simp only [L220_row]
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  congr 1
  rw [L220_tau_add L220_comm, L220_comm (L220_tau σ μ), Polynomial.mapEquiv_apply,
    Polynomial.map_map]
  rfl

end L220_main

theorem solution {K F : Type*} [Field K] [Field F] [Finite F] [Algebra K F] {g d : ℕ}
    (hg : 1 ≤ g) (hd : 1 ≤ d) (σ : Fin g → (F ≃ₐ[K] F))
    (hσ : Subgroup.closure (Set.range σ) = ⊤) (u : Fin d → F[X])
    (hu : letI := ratFuncAlgebra K F
      LinearIndependent (RatFunc K) fun a => algebraMap F[X] (RatFunc F) (u a)) :
    ∃ B : Finset (Fin g → ℕ), IsConjugateSet K σ u B := by
  set r : (Fin g → ℕ) → (Fin d → RatFunc F) := fun ω => L220_row u (L220_tau σ ω) with hr
  have htop : Submodule.span (RatFunc F) (Set.range r) = ⊤ := by
    rw [eq_top_iff, ← L220_span_top u hu, Submodule.span_le]
    rintro _ ⟨τ, rfl⟩
    obtain ⟨ω, hω⟩ := L220_tau_surj L220_comm σ hσ τ
    exact Submodule.subset_span ⟨ω, by
      show L220_row u (L220_tau σ ω) = _
      rw [hω]⟩
  have hshift : ∀ (ν δ : Fin g → ℕ) (T : Set (Fin g → ℕ)),
      r ν ∈ Submodule.span (RatFunc F) (r '' T) →
      r (ν + δ) ∈ Submodule.span (RatFunc F) (r '' ((· + δ) '' T)) := by
    intro ν δ T h
    have := L220_span_map (IsFractionRing.ringEquivOfRingEquiv (K := RatFunc F)
      (L := RatFunc F) (Polynomial.mapEquiv (L220_tau σ δ).toRingEquiv)).toRingHom _ _ h
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at this
    have hrs : ∀ μ, (fun a => (IsFractionRing.ringEquivOfRingEquiv (K := RatFunc F)
        (L := RatFunc F) (Polynomial.mapEquiv (L220_tau σ δ).toRingEquiv)) (r μ a)) =
        r (μ + δ) := fun μ => L220_row_shift u σ μ δ
    have hset : (fun w a => (IsFractionRing.ringEquivOfRingEquiv (K := RatFunc F)
        (L := RatFunc F) (Polynomial.mapEquiv (L220_tau σ δ).toRingEquiv)) (w a)) '' (r '' T) =
        r '' ((· + δ) '' T) := by
      rw [Set.image_image, Set.image_image]
      exact Set.image_congr fun μ _ => hrs μ
    rw [hset, hrs ν] at this
    exact this
  obtain ⟨B, hcard, hdown, hli⟩ := L220_greedy r htop hshift
  refine ⟨B, hcard, hdown, ?_, ?_⟩
  · intro e
    set M : Matrix (Fin d) (Fin d) F[X] := Matrix.of fun (x a : Fin d) =>
      (u a).map ((List.ofFn fun j => σ j ^ (e x : Fin g → ℕ) j).prod).toRingEquiv.toRingHom
      with hM
    intro hdet
    have hrows : LinearIndependent (RatFunc F)
        (fun x => ((algebraMap F[X] (RatFunc F)).mapMatrix M) x) := by
      have := hli.comp e e.injective
      convert this using 1
      funext x a
      rfl
    have hunit := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    rw [Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det, hdet, map_zero] at hunit
    exact not_isUnit_zero hunit
  · intro n α _
    exact L220_move hd σ B hcard hdown n α
