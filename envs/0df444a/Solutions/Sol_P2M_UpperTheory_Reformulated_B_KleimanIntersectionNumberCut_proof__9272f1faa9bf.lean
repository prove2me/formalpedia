-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_KleimanIntersectionNumberCut_proof__9272f1faa9bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:30:09.057115+00:00
-- url     : https://prove2.me/submissions/0195e01d-29b7-41bb-ad2d-10dd106e243e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StMixedTwistShift
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StCutRestrLenExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TensorSubInsertion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_monos_isHomogeneous_bb0f48dbdc12

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option maxSynthPendingDepth 1
namespace UpperTheory.Reformulated.B.KleimanIntersectionNumberCut.SlopeTestRemainingChoices
open GroundTheory.Heights₂.Heights.Kleiman MvPolynomial Filter
noncomputable section
universe u w
private theorem dim_lt {R : Type*} [CommRing R] {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (hpq : p ≤ q) {r : R} (hrq : r ∈ q) (hrp : r ∉ p) {m : ℕ}
    (h : ringKrullDim (R ⧸ p) ≤ ((m + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (R ⧸ q) ≤ ((m : ℕ) : WithBot ℕ∞) := by
  have hr : Ideal.Quotient.mk p r ∈ nonZeroDivisors (R ⧸ p) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  let φ : (R ⧸ p) →+* (R ⧸ q) := Ideal.Quotient.factor hpq
  have hφ : Function.Surjective φ := Ideal.Quotient.factor_surjective hpq
  let ψ : ((R ⧸ p) ⧸ Ideal.span {Ideal.Quotient.mk p r}) →+* (R ⧸ q) :=
    Ideal.Quotient.lift _ φ (by
      intro a ha
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      have : φ (Ideal.Quotient.mk p r) = 0 := by
        change Ideal.Quotient.mk q r = 0
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hrq
      rw [map_mul, this, mul_zero])
  have hψ : Function.Surjective ψ := Ideal.Quotient.lift_surjective_of_surjective _ _ hφ
  have h2 := ringKrullDim_le_of_surjective ψ hψ
  have h3 : ringKrullDim (R ⧸ q) + 1 ≤ ((m + 1 : ℕ) : WithBot ℕ∞) :=
    (add_le_add_left h2 1).trans (h1.trans h)
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q) := ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim (R ⧸ q) = a at h3 h0
  induction a with
  | bot => simp at h0
  | coe a =>
    induction a with
    | top =>
      exfalso
      have : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := rfl
      rw [this] at h3
      exact absurd (WithBot.coe_le_coe.mp h3) (by simp)
    | coe a =>
      have h4 : ((a + 1 : ℕ) : WithBot ℕ∞) ≤ ((m + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h3
      have h5 : a + 1 ≤ m + 1 := by exact_mod_cast h4
      have h6 : a ≤ m := by omega
      exact_mod_cast h6
section Tensor
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
private theorem foldl_line {n : ℕ} (L : Fin n → LineBundle S x) (l : List (Fin n))
    (Q₀ : LineBundle S x) : ∃ Q : LineBundle S x, Q.toSubSystem =
      l.foldl (fun F i => F.twist (L i).toSubSystem) Q₀.toSubSystem := by
  induction l generalizing Q₀ with
  | nil => exact ⟨Q₀, rfl⟩
  | cons a l ih => exact ih (tens Q₀ (L a))
private theorem tensorSub_line {n : ℕ} (L : Fin n → LineBundle S x) (T : Finset (Fin n)) :
    ∃ Q : LineBundle S x, Q.toSubSystem = tensorSub (fun i => (L i).toSubSystem) T :=
  foldl_line L _ (twistBundle S x 0)
end Tensor
section Form
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
private theorem monos_insert_factor (I : Finset (Fin (N + 1))) (i : Fin (N + 1)) {τ : Poly k N}
    (h : τ ∈ monos (S := k) (insert i I)) :
    ∃ (τ' : Poly k N) (r : ℕ), τ' ∈ monos (S := k) I ∧ τ = τ' * X i ^ r := by
  induction h using Submonoid.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    rcases Finset.mem_insert.mp (by exact_mod_cast hj) with rfl | hj'
    · exact ⟨1, 1, one_mem _, by simp⟩
    · exact ⟨X j, 0, X_mem_monos hj', by simp⟩
  | one => exact ⟨1, 0, one_mem _, by simp⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a', r, ha', rfl⟩ := ha
    obtain ⟨b', r', hb', rfl⟩ := hb
    exact ⟨a' * b', r + r', mul_mem ha' hb', by ring⟩
private theorem exists_form (Lc : LineBundle k x) (s : Ω) (pp : Ideal (Poly k N))
    (hs : s ∈ Lc.secs) (hnz : ∃ I, s ∉ (Lc.twist (idealSys x pp)).sub I) :
    ∃ f ∈ zeroIdeal Lc.toSubSystem s, f ∉ pp := by
  classical
  obtain ⟨I₀, hI₀⟩ := hnz
  obtain ⟨i, hi⟩ := I₀.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I₀.2.2 hi)
  let C : Chart x := singleChart hxi
  have hCI : C.1 ⊆ I₀.1 := Finset.singleton_subset_iff.mpr hi
  have hsC : s ∉ (Lc.twist (idealSys x pp)).sub C :=
    fun h => hI₀ (SubSystem.mono _ C I₀ hCI s h)
  have hsD : s ∈ Lc.sub C := (Submodule.mem_iInf _).mp hs C
  obtain ⟨D', hD'⟩ := Lc.invertible C
  obtain ⟨e, he, hse⟩ : ∃ e ∈ D', s * e ∉ idealMod pp C := by
    by_contra! hall
    apply hsC
    have key : ∀ z ∈ Lc.sub C * D', s * z ∈ (Lc.twist (idealSys x pp)).sub C := by
      intro z hz
      refine Submodule.mul_induction_on hz ?_ ?_
      · intro δ hδ e he
        refine Submodule.subset_span ⟨s * e, hall e he, δ, hδ, ?_⟩
        rw [smul_eq_mul]; ring
      · intro a b ha hb
        rw [mul_add]; exact add_mem ha hb
    have := key 1 (by rw [hD']; exact Submodule.one_le.mp le_rfl)
    simpa using this
  have ha1 : s * e ∈ (1 : Submodule (chartRing k x C) Ω) := hD' ▸ Submodule.mul_mem_mul hsD he
  obtain ⟨r₀, hr₀⟩ := Submodule.mem_one.mp ha1
  obtain ⟨g, t, m, ht, hg, htm, hrv⟩ := r₀.2
  have hr₀' : (r₀ : Ω) = s * e := hr₀
  have ht' : t ∈ Submonoid.closure {(X i : Poly k N)} := by
    have : ((fun j => (X j : Poly k N)) '' (((C.1 : Finset (Fin (N + 1))) : Set (Fin (N + 1))))) =
        {X i} := by simp [C, singleChart]
    rw [← this]; exact ht
  obtain ⟨m', rfl⟩ := Submonoid.mem_closure_singleton.mp ht'
  have hmm : m = m' := htm.inj_right (isHomogeneous_X_pow i m') (by
    rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
  subst hmm
  have hgv : aeval x g = s * e * x i ^ m := by
    rw [← hr₀', hrv, map_pow, aeval_X]
    field_simp
  have hchart : ∀ I : Chart x, ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ δ ∈ Lc.sub I,
      x i ^ n * e * δ ∈ twistMod k x (n : ℤ) I := by
    intro I
    let K : Chart x := ⟨insert i I.1, Finset.insert_nonempty _ _,
      Finset.insert_subset ((mem_support x).mpr hxi) I.2.2⟩
    have hIK : I.1 ⊆ K.1 := Finset.subset_insert _ _
    have hCK : C.1 ⊆ K.1 := Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)
    have one : ∀ δ ∈ Lc.sub I, ∃ r : ℕ, ∀ n ≥ r, x i ^ n * e * δ ∈ twistMod k x (n : ℤ) I := by
      intro δ hδ
      have hδK := Lc.mono I K hIK δ hδ
      obtain ⟨u, ⟨v, hv⟩, huδ⟩ := (Lc.mem_iff C K hCK δ).mp hδK
      have h1 : ((u : Ω) • δ) * e ∈ (1 : Submodule (chartRing k x C) Ω) :=
        hD' ▸ Submodule.mul_mem_mul huδ he
      obtain ⟨r', hr'⟩ := Submodule.mem_one.mp h1
      have hr'' : (r' : Ω) = (u : Ω) * δ * e := hr'
      let y : chartRing k x K := ↑v⁻¹ * chartIncl hCK r'
      have hinv : ((↑v⁻¹ : chartRing k x K) : Ω) * (u : Ω) = 1 := by
        have := congrArg Subtype.val (Units.inv_mul v)
        rw [hv] at this
        exact this
      have hy : (y : Ω) = e * δ := by
        change ((↑v⁻¹ : chartRing k x K) : Ω) * (r' : Ω) = e * δ
        rw [hr'']
        linear_combination (δ * e) * hinv
      obtain ⟨b, τ, ε, hτ, hb, hτε, hyv⟩ := y.2
      obtain ⟨τ', r, hτ', rfl⟩ := monos_insert_factor I.1 i hτ
      obtain ⟨e', he'⟩ := monos_isHomogeneous hτ'
      have hτ0 : aeval x τ' ≠ 0 := eval_ne_zero_of_mem_monos I hτ'
      have hne : τ' * X i ^ r ≠ 0 := by
        intro h0
        have := eval_ne_zero_of_mem_monos K hτ
        rw [h0, map_zero] at this
        exact this rfl
      have hεq : ε = e' + r := hτε.inj_right (he'.mul (isHomogeneous_X_pow i r)) hne
      refine ⟨r, fun n hn => ?_⟩
      have hval : x i ^ n * e * δ = aeval x (X i ^ (n - r) * b) / aeval x τ' := by
        have hn' : x i ^ n = x i ^ (n - r) * x i ^ r := by
          rw [← pow_add, Nat.sub_add_cancel hn]
        rw [mul_assoc, ← hy, hyv, map_mul, map_mul, map_pow, map_pow, aeval_X, hn']
        field_simp
      rw [hval]
      refine Submodule.subset_span ⟨X i ^ (n - r) * b, τ', e', n - r + ε, hτ',
        (isHomogeneous_X_pow i (n - r)).mul hb, he', ?_, rfl⟩
      push_cast [hεq, Nat.cast_sub hn]
      ring
    obtain ⟨T, hT⟩ := Lc.fg I
    have hTm : ∀ δ ∈ T, δ ∈ Lc.sub I := fun δ h => hT ▸ Submodule.subset_span h
    choose! r hr using fun δ (h : δ ∈ T) => one δ (hTm δ h)
    refine ⟨T.sup r, fun n hn δ hδ => ?_⟩
    rw [← hT] at hδ
    refine Submodule.span_induction (p := fun δ _ => x i ^ n * e * δ ∈ twistMod k x (n : ℤ) I)
      ?_ ?_ ?_ ?_ hδ
    · intro z hz
      exact hr z hz n ((Finset.le_sup hz).trans hn)
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      rw [mul_add]; exact add_mem ha hb
    · intro a z _ hz
      have := Submodule.smul_mem _ a hz
      rw [chartRing_smul_def] at this ⊢
      have e2 : x i ^ n * e * ((a : Ω) * z) = (a : Ω) * (x i ^ n * e * z) := by ring
      rw [e2]; exact this
  choose n₀ hn₀ using hchart
  obtain ⟨n, hnm, hn⟩ : ∃ n, m ≤ n ∧ ∀ I, n₀ I ≤ n :=
    ⟨Finset.univ.sup n₀ + m, by omega, fun I =>
      (Finset.le_sup (Finset.mem_univ I)).trans (Nat.le_add_right _ _)⟩
  have hfh : (g * X i ^ (n - m)).IsHomogeneous n := by
    have := hg.mul (isHomogeneous_X_pow (R := k) i (n - m))
    rwa [Nat.add_sub_cancel' hnm] at this
  have hfv : aeval x (g * X i ^ (n - m)) = s * e * x i ^ n := by
    rw [map_mul, hgv, map_pow, aeval_X, mul_assoc, ← pow_add, Nat.add_sub_cancel' hnm]
  refine ⟨g * X i ^ (n - m), Ideal.subset_span ⟨n, hfh, fun I δ hδ =>
    ⟨x i ^ n * e * δ, hn₀ I n (hn I) δ hδ, ?_⟩⟩, fun hf => hse ?_⟩
  · rw [hfv]; ring
  · refine Submodule.subset_span ⟨g * X i ^ (n - m), X i ^ n, n, hf,
      pow_mem (X_mem_monos (Finset.mem_singleton_self i)) n, hfh, isHomogeneous_X_pow i n, ?_⟩
    rw [hfv, map_pow, aeval_X]
    field_simp
end Form
section Mixed
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
private theorem filter_map_cast {n : ℕ} (T : Finset (Fin n)) :
    (List.finRange (n + 1)).filter (· ∈ T.map Fin.castSuccEmb) =
      ((List.finRange n).filter (· ∈ T)).map Fin.castSucc := by
  rw [List.finRange_succ_last, List.filter_append, List.filter_map]
  have h1 : List.filter (fun i => decide (i ∈ T.map Fin.castSuccEmb)) [Fin.last n] = [] := by
    simp
  rw [h1, List.append_nil]
  congr 2
  funext i
  simp
private theorem filter_insert_cast {n : ℕ} (T : Finset (Fin n)) :
    (List.finRange (n + 1)).filter (· ∈ insert (Fin.last n) (T.map Fin.castSuccEmb)) =
      ((List.finRange n).filter (· ∈ T)).map Fin.castSucc ++ [Fin.last n] := by
  rw [List.finRange_succ_last, List.filter_append, List.filter_map]
  have h1 : List.filter (fun i => decide (i ∈ insert (Fin.last n) (T.map Fin.castSuccEmb)))
      [Fin.last n] = [Fin.last n] := by
    simp
  rw [h1]
  congr 3
  funext i
  simp [Fin.castSucc_ne_last]
private theorem tensorSub_map {n : ℕ} (L : Fin n → SubSystem S x Ω) (M : SubSystem S x Ω)
    (T : Finset (Fin n)) :
    tensorSub (Fin.snoc (α := fun _ => SubSystem S x Ω) L M) (T.map Fin.castSuccEmb) =
      tensorSub L T := by
  unfold tensorSub
  rw [filter_map_cast, List.foldl_map]
  simp only [Fin.snoc_castSucc]
private theorem tensorSub_insert {n : ℕ} (L : Fin n → SubSystem S x Ω) (M : SubSystem S x Ω)
    (T : Finset (Fin n)) :
    tensorSub (Fin.snoc (α := fun _ => SubSystem S x Ω) L M)
        (insert (Fin.last n) (T.map Fin.castSuccEmb)) = (tensorSub L T).twist M := by
  unfold tensorSub
  rw [filter_insert_cast, List.foldl_append, List.foldl_map]
  simp only [Fin.snoc_castSucc, List.foldl_cons, List.foldl_nil, Fin.snoc_last]
private theorem sum_powerset_map {n : ℕ} (f : Finset (Fin (n + 1)) → ℤ) :
    ∑ t ∈ ((Finset.univ : Finset (Fin n)).map Fin.castSuccEmb).powerset, f t =
      ∑ T : Finset (Fin n), f (T.map Fin.castSuccEmb) := by
  symm
  refine Finset.sum_bij (fun T _ => T.map Fin.castSuccEmb) ?_ ?_ ?_ ?_
  · intro T _
    exact Finset.mem_powerset.mpr (Finset.map_subset_map.mpr (Finset.subset_univ _))
  · intro a _ b _ h
    exact Finset.map_injective _ h
  · intro t ht
    obtain ⟨u, -, rfl⟩ := Finset.subset_map_iff.mp (Finset.mem_powerset.mp ht)
    exact ⟨u, Finset.mem_univ _, rfl⟩
  · intro _ _
    rfl
private theorem interSum_snoc (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    (M : SubSystem S x Ω) (c : ℕ) :
    interSum pp (Fin.snoc (α := fun _ => SubSystem S x Ω) L M) c =
      ∑ T : Finset (Fin n), (-1 : ℤ) ^ (n - T.card) *
        (restrLen pp (((tensorSub L T).twist M).twist (twistSys S x (c : ℤ))) -
          restrLen pp ((tensorSub L T).twist (twistSys S x (c : ℤ)))) := by
  classical
  unfold interSum
  have huniv : (Finset.univ : Finset (Fin (n + 1))) =
      insert (Fin.last n) ((Finset.univ : Finset (Fin n)).map Fin.castSuccEmb) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
  have hnot : Fin.last n ∉ (Finset.univ : Finset (Fin n)).map Fin.castSuccEmb := by
    simp [Fin.castSucc_ne_last]
  rw [← Finset.powerset_univ, huniv, Finset.sum_powerset_insert hnot, sum_powerset_map,
    sum_powerset_map, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hnT : Fin.last n ∉ T.map Fin.castSuccEmb := by simp [Fin.castSucc_ne_last]
  have hc : T.card ≤ n := by simpa using T.card_le_univ
  rw [Finset.card_insert_of_notMem hnT, Finset.card_map, tensorSub_map, tensorSub_insert,
    show n + 1 - T.card = (n - T.card) + 1 by omega, show n + 1 - (T.card + 1) = n - T.card by omega,
    pow_succ]
  ring
end Mixed
section Final
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
private theorem span_homog (Gs : Set (Poly k N)) (h : ∀ f ∈ Gs, ∃ c : ℕ, f.IsHomogeneous c) :
    ∀ p ∈ Ideal.span Gs, ∀ d : ℕ, homogeneousComponent d p ∈ Ideal.span Gs := by
  classical
  letI : GradedAlgebra (homogeneousSubmodule (Fin (N + 1)) k) := gradedAlgebra
  have hh : (Ideal.span Gs).IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) :=
    Ideal.homogeneous_span _ _ fun f hf => by
      obtain ⟨c, hc⟩ := h f hf
      exact ⟨c, (mem_homogeneousSubmodule c f).mpr hc⟩
  intro p hp d
  have := hh d hp
  have e : ((DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) k) p d :
      homogeneousSubmodule (Fin (N + 1)) k d) : Poly k N) = homogeneousComponent d p :=
    decomposition.decompose'_apply p d
  rwa [e] at this
private theorem sup_homog {A B : Ideal (Poly k N)}
    (hA : ∀ p ∈ A, ∀ d : ℕ, homogeneousComponent d p ∈ A)
    (hB : ∀ p ∈ B, ∀ d : ℕ, homogeneousComponent d p ∈ B) :
    ∀ p ∈ A ⊔ B, ∀ d : ℕ, homogeneousComponent d p ∈ A ⊔ B := by
  intro p hp d
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hp
  rw [map_add]
  exact add_mem (Ideal.mem_sup_left (hA a ha d)) (Ideal.mem_sup_right (hB b hb d))
open Classical in
private theorem sum_eq_finsum (x : Fin (N + 1) → Ω) (n : ℕ) (J : Ideal (Poly k N))
    (Ls : Fin n → SubSystem k x Ω) (m : ℕ) (P : Fin m → Ideal (Poly k N))
    (hcard : ∀ (G : Ideal (Poly k N)) [G.IsPrime], G ∈ J.minimalPrimes →
      (((Finset.univ.filter fun j => P j = G).card : ℕ) : ℕ∞) = cutMult J G)
    (hmin : ∀ j, IsSubvar x (P j) n → P j ∈ J.minimalPrimes) :
    ∑ j, (if IsSubvar x (P j) n then interNum (P j) Ls else 0) =
      ∑ᶠ qq : Ideal (Poly k N),
        if h : qq ∈ J.minimalPrimes ∧ IsSubvar x qq n then
          haveI : qq.IsPrime := h.1.1.1
          ((cutMult J qq).toNat : ℤ) * interNum qq Ls
        else 0 := by
  have hsupp : Function.support (fun qq : Ideal (Poly k N) =>
      if h : qq ∈ J.minimalPrimes ∧ IsSubvar x qq n then
        haveI : qq.IsPrime := h.1.1.1
        ((cutMult J qq).toNat : ℤ) * interNum qq Ls
      else 0) ⊆ ↑(Finset.univ.image P) := by
    intro qq hq
    by_contra hnot
    apply hq
    dsimp only
    split_ifs with h
    · haveI : qq.IsPrime := h.1.1.1
      have hc := hcard qq h.1
      have h0 : (Finset.univ.filter fun j => P j = qq).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun j _ hj =>
          hnot (by simpa using ⟨j, hj⟩))
      rw [h0] at hc
      rw [← hc]
      simp
    · rfl
  rw [finsum_eq_sum_of_support_subset _ hsupp,
    Finset.sum_comp (fun q => if IsSubvar x q n then interNum q Ls else 0) P]
  refine Finset.sum_congr rfl fun G hG => ?_
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hG
  by_cases h : IsSubvar x (P j) n
  · have hm := hmin j h
    haveI : (P j).IsPrime := h.isPrime
    have hc := hcard (P j) hm
    rw [if_pos h, dif_pos ⟨hm, h⟩, ← hc, ENat.toNat_coe, nsmul_eq_mul]
  · rw [if_neg h, dif_neg (fun h' => h h'.2), smul_zero]
private theorem main : CycleSplit.Filt.Statement.{u, w} → CutRestrLenExact.Statement.{u, w} →
    MixedTwistShift.Statement.{u, w} → InterNumCut.Statement.{u, w} := by
  intro hCyc hCut hMix k _ Ω _ _ N x n pp L Lc s hsub hs hnz
  classical
  have hle : pp ≤ pp ⊔ zeroIdeal Lc.toSubSystem s := le_sup_left
  obtain ⟨f, hfZ, hfp⟩ := exists_form Lc s pp hs hnz
  have hfJ : f ∈ pp ⊔ zeroIdeal Lc.toSubSystem s := Ideal.mem_sup_right hfZ
  haveI := hsub.isPrime
  have hJh : ∀ p ∈ pp ⊔ zeroIdeal Lc.toSubSystem s, ∀ d : ℕ,
      homogeneousComponent d p ∈ pp ⊔ zeroIdeal Lc.toSubSystem s :=
    sup_homog hsub.homog (span_homog _ fun f ⟨c, hc, _⟩ => ⟨c, hc⟩)
  obtain ⟨m, P, d, hP, hcard, hsplit⟩ := hCyc k Ω N x ⊥ Ideal.bot_isMaximal _ hJh
    (hsub.le.trans hle) (by rw [Ideal.map_bot]; exact bot_le)
  have hdim : ∀ q : Ideal (Poly k N), q.IsPrime → pp ⊔ zeroIdeal Lc.toSubSystem s ≤ q →
      ringKrullDim (Poly k N ⧸ q) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by
    intro q hq hJq
    exact dim_lt (hle.trans hJq) (hJq hfJ) hfp hsub.dim.le
  have hmin : ∀ j, IsSubvar x (P j) n → P j ∈ (pp ⊔ zeroIdeal Lc.toSubSystem s).minimalPrimes := by
    intro j hj
    haveI := hj.isPrime
    obtain ⟨G, hG, hGP⟩ := Ideal.exists_minimalPrimes_le (hP j).2.2
    haveI : G.IsPrime := hG.1.1
    by_cases hPG : P j ≤ G
    · rwa [← le_antisymm hGP hPG]
    · exfalso
      obtain ⟨r, hr, hrG⟩ := SetLike.not_le_iff_exists.mp hPG
      have h1 := dim_lt hGP hr hrG (hdim G hG.1.1 hG.1.2)
      rw [hj.dim] at h1
      have h2 : n + 1 ≤ n := by exact_mod_cast h1
      omega
  choose Q hQ using fun T : Finset (Fin n) => tensorSub_line L T
  have E1 := eventually_all.mpr fun T => hCut k Ω N x (n + 1) pp Lc s hsub hs hnz (Q T)
  have E2 := eventually_all.mpr fun T => hsplit (tens (Q T) Lc)
  have E3 := eventually_all.mpr fun j => hMix k Ω N x n (P j) (hP j).1 (hP j).2.1
    (hsub.le.trans (hle.trans (hP j).2.2)) (hdim _ (hP j).1 (hP j).2.2) L Lc (d j)
  have hev : interSum pp (Fin.snoc (α := fun _ => SubSystem k x Ω)
      (fun i => (L i).toSubSystem) Lc.toSubSystem) =ᶠ[atTop]
      fun _ => ∑ j, (if IsSubvar x (P j) n then
        interNum (P j) (fun i => (L i).toSubSystem) else 0) := by
    filter_upwards [E1, E2, E3] with c h1 h2 h3
    rw [interSum_snoc]
    have hT : ∀ T : Finset (Fin n),
        restrLen pp (((tensorSub (fun i => (L i).toSubSystem) T).twist Lc.toSubSystem).twist
            (twistSys k x (c : ℤ))) -
          restrLen pp ((tensorSub (fun i => (L i).toSubSystem) T).twist (twistSys k x (c : ℤ))) =
        ∑ j, restrLen (P j) (((tensorSub (fun i => (L i).toSubSystem) T).twist
          Lc.toSubSystem).twist (twistSys k x ((c : ℤ) + d j))) := by
      intro T
      have a1 := h1 T
      have a2 := h2 T
      rw [← hQ T]
      exact a1.trans a2
    simp_rw [hT, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => h3 j
  rw [interNum, (tendsto_const_nhds.congr' hev.symm).limUnder_eq]
  exact sum_eq_finsum x n _ _ m P hcard hmin
end Final
end
end UpperTheory.Reformulated.B.KleimanIntersectionNumberCut.SlopeTestRemainingChoices
end

set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace UpperTheory.Reformulated.B.KleimanIntersectionNumberCut.proof
theorem _root_.solution.{u, w} :
    GroundTheory.Heights₂.Heights.Kleiman.CycleSplit.Filt.Statement.{u, w} →
      GroundTheory.Heights₂.Heights.Kleiman.CutRestrLenExact.Statement.{u, w} →
        GroundTheory.Heights₂.Heights.Kleiman.MixedTwistShift.Statement.{u, w} →
          GroundTheory.Heights₂.Heights.Kleiman.InterNumCut.Statement.{u, w} := by
  exact UpperTheory.Reformulated.B.KleimanIntersectionNumberCut.SlopeTestRemainingChoices.main
end UpperTheory.Reformulated.B.KleimanIntersectionNumberCut.proof
