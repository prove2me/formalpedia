-- Prove2me | solution 3 for WeierstrassEllipticZeta.finite_set_projective_multiplicity_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-23T22:23:35.720384+00:00
-- url     : https://prove2.me/submissions/c293ae37-2af7-4cd9-936d-790cfb227bf6

import Theorems.Thm_PhilipponMultiplicity_theorem_2_1
import Theorems.Thm_PhilipponMultiplicity_lemma_3_4
import Theorems.Thm_PhilipponMultiplicity_analytic_contact_invariance
import Theorems.Thm_TranscendenceTheory_projective_chart_vanishing_order
import Theorems.Thm_WeierstrassEllipticZeta_philippon_model_realization
import Theorems.Thm_WeierstrassEllipticZeta_philippon_subgroup_degree_profile

set_option autoImplicit false
open WeierstrassEllipticZeta WeierstrassEllipticZeta.PhilipponApplication
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open scoped BigOperators Pointwise Classical
noncomputable section

private lemma complex_base : IsPhilipponBaseField ℂ :=
  Or.inl ⟨RingEquiv.refl ℂ, isometry_id⟩

private lemma model_dimension {S : Fin 5 → ℂ → ℂ} (M : Model S) :
    M.group.dimension = 3 := by
  change ∑ i : Fin 2, (M.factor i).dimension = 3
  simp [M.factor_dimension, Fin.sum_univ_two]

private lemma raw_order_implies_contact {S : Fin 5 → ℂ → ℂ} (M : Model S)
    (Q : MvPolynomial (Fin 7) ℂ) (v : ℂ) (k : ℕ)
    (hf : AnalyticAt ℂ (fun z => MvPolynomial.eval (rawCoordinates S z) Q) v)
    (horder : (k : ℕ∞) ≤ analyticOrderAt
      (fun z => MvPolynomial.eval (rawCoordinates S z) Q) v) :
    (k : WithTop ℕ) ≤ vanishingOrder M.A (M.polynomial Q) (M.curve v) := by
  let f : ℂ → ℂ := fun z => MvPolynomial.eval (rawCoordinates S z) Q
  have hderiv := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mp horder
  unfold vanishingOrder
  apply le_sInf
  rintro _ ⟨i, hi, rfl⟩
  by_contra! hlt
  have hik : i < k := by exact_mod_cast hlt
  apply hi
  have hz : iteratedFDeriv ℂ i (fun z => f (v + z)) 0 = 0 := by
    have hz' : iteratedDeriv i (fun z => f (v + z)) 0 = 0 := by
      rw [iteratedDeriv_comp_const_add]
      simpa [f] using hderiv i hik
    simp only [iteratedFDeriv_eq_equiv_comp, Function.comp_apply, hz', map_zero]
  have hcomp := M.parameter.iteratedFDerivWithin_comp_right
    (fun z => f (v + z)) uniqueDiffOn_univ (Set.mem_univ _) i (x := 0)
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ, map_zero, hz] at hcomp
  have hp : M.A.pullback (M.polynomial Q) (M.curve v) =
      (fun z => f (v + z)) ∘ M.parameter := by
    funext t
    exact M.pullback Q v t
  rw [hp, hcomp]
  ext t
  simp

private lemma chart_order_implies_contact {S : Fin 5 → ℂ → ℂ} (M : Model S)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (hQ : Bihomogeneous Q m n)
    (v : ℂ) (j : Fin 5) (hj : S j v ≠ 0) (k : ℕ)
    (horder : (k : ℕ∞) ≤ analyticOrderAt (fun z => MvPolynomial.eval
      ![1, z, S 0 z / S j z, S 1 z / S j z, S 2 z / S j z,
        S 3 z / S j z, S 4 z / S j z] Q) v) :
    (k : WithTop ℕ) ≤ vanishingOrder M.A (M.polynomial Q) (M.curve v) := by
  have hA : ∀ i : Fin 2, AnalyticAt ℂ ((![fun _ : ℂ => 1, id] : Fin 2 → ℂ → ℂ) i) v := by
    intro i
    fin_cases i
    · exact analyticAt_const
    · exact analyticAt_id
  obtain ⟨hraw, _, heq, _⟩ := TranscendenceTheory.projective_chart_vanishing_order
    ![fun _ : ℂ => 1, id] S Q n (fun d hd => (hQ d hd).2) v j hj hA
      (fun i => hS i v trivial)
  apply raw_order_implies_contact M Q v k
  · exact hraw
  · exact le_trans horder (le_of_eq heq.symm)

private lemma sample_sumset {S : Fin 5 → ℂ → ℂ} (M : Model S)
    (X : Finset ℂ) (g : M.group.Point)
    (hg : g ∈ sumset (X.image M.curve) M.group.dimension) :
    ∃ v ∈ X + X + X, g = M.curve v := by
  classical
  rw [model_dimension] at hg
  have hex : ∃ f : Fin 3 → {y // y ∈ X.image M.curve}, (∑ i, (f i).val) = g := by
    simpa only [sumset, Finset.mem_image, Finset.mem_univ, true_and] using hg
  obtain ⟨f, rfl⟩ := hex
  obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp (f 0).property
  obtain ⟨y, hy, hfy⟩ := Finset.mem_image.mp (f 1).property
  obtain ⟨z, hz, hfz⟩ := Finset.mem_image.mp (f 2).property
  refine ⟨x + y + z, Finset.add_mem_add (Finset.add_mem_add hx hy) hz, ?_⟩
  simp [Fin.sum_univ_three, ← hfx, ← hfy, ← hfz]

private lemma proper_obstruction {S : Fin 5 → ℂ → ℂ} (M : Model S)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (hQ : Bihomogeneous Q m n)
    (hne : (fun z => MvPolynomial.eval (rawCoordinates S z) Q) ≠ 0)
    (H : AlgebraicSubgroup M.group)
    (hzero : ∃ g, H.carrier ⊆ PhilipponMultiplicity.translate g
      (zeroLocusOnGroup M.group (M.polynomial Q))) :
    H.carrier ≠ Set.univ := by
  intro hall
  obtain ⟨g, hg⟩ := hzero
  apply hne
  funext z
  have hmem : g + M.curve z ∈ H.carrier := by rw [hall]; trivial
  obtain ⟨w, hw, heq⟩ := hg hmem
  have hwz : w = M.curve z := add_left_cancel heq
  subst w
  exact (M.zero_locus Q m n hQ z).mp hw

private lemma obstruction_codimension {S : Fin 5 → ℂ → ℂ} (M : Model S)
    (H : AlgebraicSubgroup M.group) (hproper : H.carrier ≠ Set.univ) :
    analyticCodimension M.A H.carrier = 1 := by
  obtain ⟨hle, hiff, _⟩ := (analytic_contact_invariance ℂ complex_base M.group M.A).2 H
  rw [M.analytic_dimension] at hle
  have hne : analyticCodimension M.A H.carrier ≠ 0 := by
    intro hz
    have hsub := hiff.mp hz
    rw [M.analytic_carrier] at hsub
    letI := M.group.zariskiTopology
    have hclosed : IsClosed H.carrier := H.isClosed
    have hdense : Dense (Set.range M.curve) := M.curve_dense
    apply hproper
    exact Set.eq_univ_of_univ_subset
      (hdense.closure_eq ▸ hclosed.closure_subset_iff.mpr hsub)
  omega

private lemma ambient_degree_bound {S : Fin 5 → ℂ → ℂ} (M : Model S)
    (c : EmbeddedCommutativeGroup ℂ → ℕ) (hc : ∀ E, 1 ≤ c E) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, 1 ≤ m → 1 ≤ n →
      hilbertDegreeForm M.group Set.univ (fun i => c (M.factor i) * (![m, n] i)) ≤
        C * (m : ℝ) * (n : ℝ) ^ 2 := by
  let V : ∀ i : Fin 2, ProjectiveSubvariety ℂ (M.factor i).ambientDimension :=
    fun i => ⟨(M.factor i).carrier, (M.factor i).locallyClosed⟩
  let W := productCarrier M.group.ambient V
  have hdim : ∀ i, (V i).dimension = ![1, 2] i := M.factor_dimension
  have himage : M.group.embedding '' Set.univ = W := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact fun i => (y i).property
    · intro hx
      exact ⟨fun i => ⟨x i, hx i⟩, Set.mem_univ _, rfl⟩
  let r : ℚ := ((locusDimension M.group.ambient W).factorial : ℚ) / 2 *
    ((V 0).degree * (V 1).degree)
  let B : ℝ := (r : ℝ) * (c (M.factor 0) : ℝ) * (c (M.factor 1) : ℝ) ^ 2
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro m n hm hn
  have hp (i : Fin 2) : 1 ≤ c (M.factor i) * (![m, n] i) := by
    have ha := hc (M.factor i)
    have hb : 1 ≤ (![m, n] i) := by fin_cases i <;> assumption
    nlinarith
  have hformula := lemma_3_4 ℂ complex_base M.group.ambient V
    (fun i => c (M.factor i) * (![m, n] i)) hp
  change locusDegreeValue M.group.ambient W (fun i => c (M.factor i) * (![m, n] i)) =
    ((locusDimension M.group.ambient W).factorial : ℚ) /
      (∏ i : Fin 2, ((V i).dimension.factorial : ℚ)) *
      (∏ i : Fin 2, (V i).degree) *
      ∏ i : Fin 2, ((c (M.factor i) * (![m, n] i) : ℕ) : ℚ) ^ (V i).dimension at hformula
  simp only [Fin.prod_univ_two, hdim, Matrix.cons_val_zero, Matrix.cons_val_one,
    Nat.factorial, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, pow_one] at hformula
  have hform : hilbertDegreeForm M.group Set.univ
      (fun i => c (M.factor i) * (![m, n] i)) = B * (m : ℝ) * (n : ℝ) ^ 2 := by
    change ((locusDegreeValue M.group.ambient (M.group.embedding '' Set.univ)
      (fun i => c (M.factor i) * (![m, n] i)) : ℚ) : ℝ) = _
    rw [himage, hformula]
    dsimp only [B, r]
    push_cast
    ring
  rw [hform]
  have hB : B ≤ |B| + 1 := le_trans (le_abs_self B) (by linarith)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB (by positivity))
    (by positivity)

private lemma image_ncard_of_same_fibres {α β γ : Type*} (X : Set α)
    (f : α → β) (g : α → γ) (hfg : ∀ x y, f x = f y ↔ g x = g y) :
    (f '' X).ncard = (g '' X).ncard := by
  classical
  apply Set.ncard_congr (fun y hy => g (Classical.choose hy))
  · intro y hy
    exact ⟨Classical.choose hy, (Classical.choose_spec hy).1, rfl⟩
  · intro y z hy hz heq
    have h := (hfg _ _).mpr heq
    exact (Classical.choose_spec hy).2.symm.trans (h.trans (Classical.choose_spec hz).2)
  · rintro z ⟨x, hx, rfl⟩
    refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
    apply (hfg _ _).mp
    exact (Classical.choose_spec (show f x ∈ f '' X from ⟨x, hx, rfl⟩)).2

private lemma coset_count_pullback {S : Fin 5 → ℂ → ℂ} (M : Model S)
    (H : AlgebraicSubgroup M.group) (X : Finset ℂ) :
    cosetCount (X.image M.curve) H.carrier =
      ((M.pullbackSubmodule H).mkQ '' (X : Set ℂ)).ncard := by
  classical
  let K := M.pullbackSubmodule H
  have hfib (x y : ℂ) : K.mkQ x = K.mkQ y ↔
      PhilipponMultiplicity.translate (M.curve x) H.carrier =
        PhilipponMultiplicity.translate (M.curve y) H.carrier := by
    change (Submodule.Quotient.mk x : ℂ ⧸ K) = Submodule.Quotient.mk y ↔ _
    rw [Submodule.Quotient.eq]
    change M.curve (x - y) ∈ H.toAddSubgroup ↔ _
    symm
    change M.curve x +ᵥ (H.toAddSubgroup : Set M.group.Point) =
      M.curve y +ᵥ (H.toAddSubgroup : Set M.group.Point) ↔ _
    rw [eq_comm, leftAddCoset_eq_iff]
    simp [map_sub, sub_eq_add_neg, add_comm]
  have heq := image_ncard_of_same_fibres (X : Set ℂ) K.mkQ
    (fun x => PhilipponMultiplicity.translate (M.curve x) H.carrier) hfib
  rw [heq]
  simp only [cosetCount, Finset.image_image, Function.comp_def,
    ← Finset.coe_image, Set.ncard_coe_finset]

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ m n U : ℕ,
      1 ≤ m → 1 ≤ n → 1 ≤ U → ∀ X : Finset ℂ,
      0 ∈ X → ∀ Q : MvPolynomial (Fin 7) ℂ,
        (∀ d ∈ Q.support, d 0 + d 1 = m ∧
          d 2 + d 3 + d 4 + d 5 + d 6 = n) →
        (fun z : ℂ => MvPolynomial.eval
          ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0 →
        (∀ v ∈ X + X + X, ∀ j : Fin 5, S j v ≠ 0 →
          ((3 * U + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt
            (fun z : ℂ => MvPolynomial.eval
              ![1, z, S 0 z / S j z, S 1 z / S j z,
                S 2 z / S j z, S 3 z / S j z, S 4 z / S j z] Q) v) →
        ∃ K : Submodule ℤ ℂ, ∃ a b : ℕ,
          ((a = 1 ∧ K = ⊥) ∨ (a = 0 ∧ K ≤ L.lattice)) ∧ b ≤ 2 ∧
          ((U + 1 : ℕ) : ℝ) * (K.mkQ '' (X : Set ℂ)).ncard ≤
            C * (m : ℝ) ^ a * (n : ℝ) ^ b := by
  classical
  obtain ⟨M⟩ := philippon_model_realization L D S hS hS_value hS_ne
  obtain ⟨c, hc, hPhilippon⟩ := theorem_2_1 ℂ complex_base
  obtain ⟨C, hC, hambient⟩ := ambient_degree_bound M c hc
  refine ⟨C, hC, ?_⟩
  intro m n U hm hn hU X hX Q hQ hne horder
  have hP : M.polynomial Q ≠ 0 := by
    intro hz
    apply hne
    funext z
    have hv := M.pullback Q z 0
    change M.A.pullback (M.polynomial Q) (M.curve z) 0 = _ at hv
    rw [hz] at hv
    simpa [AnalyticSubgroup.pullback, rawCoordinates] using hv.symm
  have hsample : (0 : M.group.Point) ∈ X.image M.curve :=
    Finset.mem_image.mpr ⟨0, hX, M.curve.map_zero⟩
  have hcontact : ∀ g ∈ sumset (X.image M.curve) M.group.dimension,
      ((M.group.dimension * U + 1 : ℕ) : WithTop ℕ) ≤
        vanishingOrder M.A (M.polynomial Q) g := by
    intro g hg
    obtain ⟨v, hv, rfl⟩ := sample_sumset M X g hg
    obtain ⟨j, hj⟩ := hS_ne v
    rw [model_dimension]
    exact chart_order_implies_contact M hS Q m n hQ v j hj (3 * U + 1)
      (horder v hv j hj)
  obtain ⟨H, hH, _, hzero, hineq⟩ := hPhilippon M.group M.A (X.image M.curve)
    hsample U ![m, n] (M.polynomial Q) hP (M.homogeneous Q m n hQ) hcontact
  have hproper := proper_obstruction M Q m n hQ hne H hzero
  have hs := obstruction_codimension M H hproper
  let K := M.pullbackSubmodule H
  have hbound : ((U + 1 : ℕ) : ℝ) * (K.mkQ '' (X : Set ℂ)).ncard *
      hilbertDegreeForm M.group H.carrier ![m, n] ≤ C * (m : ℝ) * (n : ℝ) ^ 2 := by
    have h := hineq.trans (hambient m n hm hn)
    simpa [hs, coset_count_pullback, K] using h
  have hnonneg : 0 ≤ ((U + 1 : ℕ) : ℝ) * (K.mkQ '' (X : Set ℂ)).ncard := by positivity
  rcases philippon_subgroup_degree_profile L D S hS hS_value hS_ne M H hH hproper with
    ⟨hK, hdegree⟩ | ⟨hK, hdegree⟩
  · refine ⟨K, 1, 2, Or.inl ⟨rfl, hK⟩, le_rfl, ?_⟩
    simp only [pow_one]
    calc
      _ ≤ ((U + 1 : ℕ) : ℝ) * (K.mkQ '' (X : Set ℂ)).ncard *
          hilbertDegreeForm M.group H.carrier ![m, n] := by
        simpa using mul_le_mul_of_nonneg_left (hdegree m n hm hn) hnonneg
      _ ≤ _ := hbound
  · refine ⟨K, 0, 2, Or.inr ⟨rfl, hK⟩, le_rfl, ?_⟩
    simp only [pow_zero, mul_one]
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    apply (mul_le_mul_iff_left₀ hmpos).mp
    calc
      _ ≤ ((U + 1 : ℕ) : ℝ) * (K.mkQ '' (X : Set ℂ)).ncard *
          hilbertDegreeForm M.group H.carrier ![m, n] :=
        mul_le_mul_of_nonneg_left (hdegree m n hm hn) hnonneg
      _ ≤ C * (m : ℝ) * (n : ℝ) ^ 2 := hbound
      _ = _ := by ring
