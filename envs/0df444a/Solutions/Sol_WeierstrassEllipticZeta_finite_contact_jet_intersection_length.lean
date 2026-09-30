-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_contact_jet_intersection_length
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T01:04:49.124142+00:00
-- url     : https://prove2.me/submissions/99afac57-2be5-4fd4-aa39-bff8ab9e1b4a

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveContactIdeal
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.Tactic.FinCases
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
open WeierstrassEllipticZeta

private lemma split_gcd_multiplicities {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (hx : Function.Injective x) (n : ι → ℕ) (q : Polynomial ℂ) :
    let M := ∏ i, (Polynomial.X - Polynomial.C (x i)) ^ n i
    ∃ e : ι → ℕ,
      (∀ i, e i ≤ n i ∧ ∀ k ≤ n i,
        k ≤ e i ↔ (Polynomial.X - Polynomial.C (x i)) ^ k ∣ q) ∧
      (gcd M q).natDegree = ∑ i, e i := by
  classical
  let M := ∏ i, (Polynomial.X - Polynomial.C (x i)) ^ n i
  have hM : M.Monic := Polynomial.monic_prod_of_monic _ _ fun i _ =>
    (Polynomial.monic_X_sub_C (x i)).pow (n i)
  have hroots : M.roots = Finset.univ.val.bind
      (fun i : ι => n i • ({x i} : Multiset ℂ)) := by
    rw [Polynomial.roots_prod _ _ hM.ne_zero]
    simp only [Polynomial.roots_pow, Polynomial.roots_X_sub_C]
  have hmult (i : ι) : M.rootMultiplicity (x i) = n i := by
    rw [← Polynomial.count_roots, hroots, Multiset.count_bind]
    change (∑ j, (n j • ({x j} : Multiset ℂ)).count (x i)) = n i
    simp [Multiset.count_singleton, hx.eq_iff]
  let G := gcd M q
  have hG : G ≠ 0 := by
    simp only [G, ne_eq, gcd_eq_zero_iff]
    exact fun h => hM.ne_zero h.1
  have hsplit : G.Splits :=
    (Polynomial.Splits.prod (fun i _ => (Polynomial.Splits.X_sub_C (x i)).pow (n i))).of_dvd
      hM.ne_zero (gcd_dvd_left M q)
  refine ⟨fun i => G.rootMultiplicity (x i), ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · exact (Polynomial.rootMultiplicity_le_rootMultiplicity_of_dvd hM.ne_zero
        (gcd_dvd_left M q) (x i)).trans_eq (hmult i)
    · intro k hk
      rw [Polynomial.le_rootMultiplicity_iff hG, dvd_gcd_iff]
      exact and_iff_right ((Polynomial.le_rootMultiplicity_iff hM.ne_zero).mp
        ((hmult i).symm ▸ hk))
  · rw [hsplit.natDegree_eq_card_roots]
    have hs : ∀ a ∈ G.roots, a ∈ Finset.univ.image x := by
      intro a ha
      have haM := Multiset.mem_of_le
        (Polynomial.roots.le_of_dvd hM.ne_zero (gcd_dvd_left M q)) ha
      rw [hroots, Multiset.mem_bind] at haM
      obtain ⟨i, _, hi⟩ := haM
      simp only [Multiset.mem_nsmul, Multiset.mem_singleton] at hi
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.2.symm⟩
    rw [← Multiset.sum_count_eq_card hs, Finset.sum_image (fun i _ j _ h => hx h)]
    simp only [Polynomial.count_roots]

private lemma time_polynomial_jets (g₂ g₃ : ℂ) (c : Fin 2)
    (v : Fin 4 → ℂ) (p : Polynomial ℂ) (k : ℕ) :
    MvPolynomial.eval v ((extensionChartDerivation g₂ g₃ c)^[k]
      (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) p)) =
        (Polynomial.derivative^[k] p).eval (v 0) := by
  have ht : extensionChartDerivation g₂ g₃ c (MvPolynomial.X (0 : Fin 4)) = 1 := by
    fin_cases c <;> simp [extensionChartDerivation]
  have h (k : ℕ) : (extensionChartDerivation g₂ g₃ c)^[k]
      (Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) p) =
      Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (Polynomial.derivative^[k] p) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Derivation.comp_aeval_eq, ht,
        smul_eq_mul, mul_one, Function.iterate_succ_apply']
  rw [h]
  exact Polynomial.induction_on' (Polynomial.derivative^[k] p)
    (fun p q hp hq => by simp_all)
    (fun i a => by simp [Polynomial.aeval_monomial])

private lemma root_power_dvd_iff_jets (x : ℂ) (p : Polynomial ℂ) (n : ℕ) :
    (Polynomial.X - Polynomial.C x) ^ n ∣ p ↔
      ∀ k < n, (Polynomial.derivative^[k] p).eval x = 0 := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  have h (k : ℕ) : (Polynomial.derivative^[k] p).eval x =
      (k.factorial : ℂ) * (Polynomial.taylor x p).coeff k := by
    rw [← Polynomial.factorial_smul_hasseDeriv]
    simp [Polynomial.taylor_coeff, nsmul_eq_mul]
  simp_rw [h, mul_eq_zero, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _),
    false_or, Polynomial.taylor_apply]

private lemma finite_family_quotient_length
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ) (hM : M ≠ 0)
    (r : Fin 3 → Polynomial ℂ)
    (hI : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
    (K : ℕ) (f : Fin K → MvPolynomial (Fin 4) ℂ) :
    let J := I ⊔ Ideal.span (Set.range f)
    let q := Finset.univ.gcd (fun i : Fin K =>
      MvPolynomial.aeval (Fin.cons Polynomial.X r) (f i))
    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = (gcd M q).natDegree := by
  classical
  let φ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval (Fin.cons Polynomial.X r)
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  have hE : φ.comp E = AlgHom.id ℂ (Polynomial ℂ) := by
    ext
    simp [φ, E]
  have hsurj : Function.Surjective φ := fun q => ⟨E q, AlgHom.congr_fun hE q⟩
  have hcomap : I = Ideal.comap φ.toRingHom (Ideal.span {M}) := by
    ext p
    simpa only [Ideal.mem_comap, Ideal.mem_span_singleton, φ] using! hI p
  have hmap : Ideal.map φ.toRingHom I = Ideal.span {M} := by
    rw [hcomap]
    exact Ideal.map_comap_of_surjective _ hsurj _
  have hker : RingHom.ker φ.toRingHom ≤ I := by
    rw [hcomap]
    exact Ideal.ker_le_comap _
  let q := Finset.univ.gcd (fun i : Fin K => φ (f i))
  have hspan : Ideal.span (Set.range (fun i : Fin K => φ (f i))) = Ideal.span {q} := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Ideal.mem_span_singleton.mpr (Finset.gcd_dvd (Finset.mem_univ i))
    · apply Ideal.span_le.mpr
      intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      obtain ⟨a, ha⟩ := Finset.gcd_eq_sum_mul Finset.univ (fun i : Fin K => φ (f i))
      rw [show q = _ from ha]
      exact Submodule.sum_mem _ fun i _ =>
        Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  let J := I ⊔ Ideal.span (Set.range f)
  let G := gcd M q
  have hG : G ≠ 0 := by
    simp only [G, ne_eq, gcd_eq_zero_iff]
    exact fun h => hM h.1
  have hmapJ : Ideal.map φ.toRingHom J = Ideal.span {G} := by
    rw [Ideal.map_sup, hmap, Ideal.map_span, ← Set.range_comp]
    change Ideal.span {M} ⊔ Ideal.span (Set.range (fun i : Fin K => φ (f i))) = _
    rw [hspan, ← Ideal.span_insert, ← span_gcd]
  let ψ := (Ideal.Quotient.mkₐ ℂ (Ideal.span {G})).comp φ
  have hsurjψ : Function.Surjective ψ :=
    (Ideal.Quotient.mkₐ_surjective ℂ _).comp hsurj
  have hkerψ : RingHom.ker ψ.toRingHom = J := by
    have heq : RingHom.ker ψ.toRingHom = Ideal.comap φ.toRingHom (Ideal.span {G}) := by
      ext p
      change Ideal.Quotient.mk (Ideal.span {G}) (φ p) = 0 ↔ φ p ∈ Ideal.span {G}
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [heq, ← hmapJ]
    exact (Ideal.comap_map_of_surjective' φ.toRingHom hsurj J).trans
      (sup_of_le_left (hker.trans le_sup_left))
  let e : (MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ] (Polynomial ℂ ⧸ Ideal.span {G}) :=
    (Ideal.quotientEquivAlgOfEq ℂ hkerψ.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurjψ)
  have : FiniteDimensional ℂ (Polynomial ℂ ⧸ Ideal.span {G}) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hG).basis
  refine ⟨FiniteDimensional.of_injective e.toLinearMap e.injective, ?_⟩
  rw [e.toLinearEquiv.finrank_eq, finrank_quotient_span_eq_natDegree]

theorem solution
    (g₂ g₃ : ℂ) (c : Fin 2)
    (hcontact : ∀ (v : Fin 4 → ℂ) (n : ℕ) (p : MvPolynomial (Fin 4) ℂ),
      p ∈ extensionChartContactIdeal g₂ g₃ c v n ↔
        ∀ k < n, MvPolynomial.eval v ((extensionChartDerivation g₂ g₃ c)^[k] p) = 0)
    (V : Finset (Fin 4 → ℂ))
    (hV : Function.Injective (fun v : V => v.val 0)) (n : V → ℕ)
    (r : Fin 3 → Polynomial ℂ)
    (hmem : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ (⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)) ↔
        (∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ n v) ∣
          MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
    (K : ℕ) (f : Fin K → MvPolynomial (Fin 4) ℂ) :
    let I := ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
    let J := I ⊔ Ideal.span (Set.range f)
    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
    ∃ e : V → ℕ,
      (∀ v : V, e v ≤ n v ∧ ∀ k ≤ n v,
        k ≤ e v ↔ ∀ i : Fin K, ∀ j < k,
          MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[j] (f i)) = 0) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = ∑ v : V, e v := by
  classical
  let I := ⨅ v : V, extensionChartContactIdeal g₂ g₃ c v.val (n v)
  let M := ∏ v : V, (Polynomial.X - Polynomial.C (v.val 0)) ^ n v
  let φ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval (Fin.cons Polynomial.X r)
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  have hE : φ.comp E = AlgHom.id ℂ (Polynomial ℂ) := by
    ext
    simp [φ, E]
  have hM : M.Monic := Polynomial.monic_prod_of_monic _ _ fun v _ =>
    (Polynomial.monic_X_sub_C (v.val 0)).pow (n v)
  let q := Finset.univ.gcd (fun i : Fin K => φ (f i))
  obtain ⟨hfinite, hrank⟩ := finite_family_quotient_length I M hM.ne_zero r hmem K f
  obtain ⟨e, he, hsum⟩ := split_gcd_multiplicities (fun v : V => v.val 0) hV n q
  refine ⟨hfinite, e, ?_, hrank.trans hsum⟩
  intro v
  refine ⟨(he v).1, ?_⟩
  have hjet (i : Fin K) (j : ℕ) (hj : j < n v) :
      MvPolynomial.eval v.val ((extensionChartDerivation g₂ g₃ c)^[j] (f i)) =
        (Polynomial.derivative^[j] (φ (f i))).eval (v.val 0) := by
    have hdiff : f i - E (φ (f i)) ∈ I := by
      apply (hmem _).mpr
      change M ∣ φ (f i - E (φ (f i)))
      have heφ : φ (E (φ (f i))) = φ (f i) := AlgHom.congr_fun hE (φ (f i))
      rw [map_sub, heφ, sub_self]
      exact dvd_zero _
    have hz := (hcontact v.val (n v) _).mp ((Submodule.mem_iInf _).mp hdiff v) j hj
    have hsub : (extensionChartDerivation g₂ g₃ c)^[j] (f i - E (φ (f i))) =
        (extensionChartDerivation g₂ g₃ c)^[j] (f i) -
          (extensionChartDerivation g₂ g₃ c)^[j] (E (φ (f i))) := by
      simpa only [Module.End.pow_apply] using!
        ((extensionChartDerivation g₂ g₃ c).toLinearMap ^ j).map_sub (f i) (E (φ (f i)))
    rw [hsub, map_sub, sub_eq_zero] at hz
    exact hz.trans (time_polynomial_jets g₂ g₃ c v.val (φ (f i)) j)
  intro k hk
  rw [(he v).2 k hk]
  change _ ∣ Finset.univ.gcd (fun i : Fin K => φ (f i)) ↔ _
  simp only [Finset.dvd_gcd_iff, Finset.mem_univ, forall_const, root_power_dvd_iff_jets]
  exact forall_congr' fun i => forall₂_congr fun j hj => by rw [hjet i j (hj.trans_le hk)]

