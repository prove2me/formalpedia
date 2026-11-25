-- Prove2me | solution 1 for ScatCaps.Caps.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-25T07:32:40.612911+00:00
-- url     : https://prove2.me/submissions/5d09d0a6-883b-45c8-a354-bee64bfc51dc

import Mathlib
import Definitions.Def_ScatCaps_Caps_Model

open ScatCaps ScatCaps.Caps

namespace P2MHole01_ea06f50d
universe u_1
theorem solution (K : Type u_1) [inst : Field K] {r : ℕ} (u v : Fin r → K) (hu : u ≠ (0 : Fin r → K))
  (hv : v ≠ (0 : Fin r → K)) (huv : u ≠ v) (hn : ¬LinearIndependent K ![u, v]) :
  ∃ (c : K), c ≠ (0 : K) ∧ c ≠ (1 : K) ∧ v = c • u := by
  -- T : (Fin 2 →₀ K) →ₗ[K] (Fin r → K), the linear-combination map of the pair ![u, v]
  set T : (Fin 2 →₀ K) →ₗ[K] (Fin r → K) := Finsupp.linearCombination K ![u, v]
  set e0 : Fin 2 →₀ K := Finsupp.single 0 1
  set e1 : Fin 2 →₀ K := Finsupp.single 1 1
  -- T e0 = u and T e1 = v
  have he0 : T e0 = u := by simp [T, e0, Finsupp.linearCombination_single]
  have he1 : T e1 = v := by simp [T, e1, Finsupp.linearCombination_single]
  -- step 1: from ¬ LinearIndependent extract a nonzero c with T c = 0
  have hrel : ∃ (c : Fin 2 →₀ K), T c = 0 ∧ c ≠ 0 := by
    rw [linearIndependent_iff] at hn  -- hn : ¬ (∀ c, T c = 0 → c = 0)
    classical
    push Not at hn  -- hn : ∃ c, T c = 0 ∧ c ≠ 0
    exact hn
  obtain ⟨c, hTc, hcne⟩ := hrel
  -- step 2: every c : Fin 2 →₀ K decomposes as c 0 • e0 + c 1 • e1
  have hdecomp : c = c 0 • e0 + c 1 • e1 := by
    ext i
    cases i with | mk n hn =>
      have h2 : n = 0 ∨ n = 1 := by omega
      rcases h2 with (rfl | rfl)
      · simp [e0, e1]
      · simp [e0, e1]
  set a : K := c 0 with ha
  set b : K := c 1 with hb
  -- step 3: the coefficients satisfy a • u + b • v = 0
  have hdec : c = a • e0 + b • e1 := by simpa [ha, hb] using hdecomp
  have hr : a • u + b • v = 0 := by
    have hT' : T (a • e0 + b • e1) = 0 := by rw [hdec] at hTc; exact hTc
    calc
      a • u + b • v = a • T e0 + b • T e1 := by rw [← he0, ← he1]
      _ = T (a • e0) + T (b • e1) := by rw [← T.map_smul, ← T.map_smul]
      _ = T (a • e0 + b • e1) := by rw [← T.map_add]
      _ = 0 := hT'
  -- step 4: neither coefficient is zero
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push_neg at h  -- h : a = 0 ∧ b = 0
    apply hcne
    ext i
    cases i with | mk n hn =>
      have h2 : n = 0 ∨ n = 1 := by omega
      rcases h2 with (rfl | rfl)
      · simp [ha] at h ⊢
        exact h.1
      · simp [hb] at h ⊢
        exact h.2
  have ha0 : a ≠ 0 := by
    by_contra h  -- h : a = 0
    have h0 : b • v = 0 := by simpa [h, zero_smul] using hr
    have hb0 : b = 0 ∨ v = 0 := smul_eq_zero.1 h0
    cases hab with
    | inl hne => exact hne h
    | inr hne =>
      cases hb0 with
      | inl hb0 => exact hne hb0
      | inr hv0 => exact hv hv0
  have hb0 : b ≠ 0 := by
    by_contra h  -- h : b = 0
    have h0 : a • u = 0 := by simpa [h, zero_smul] using hr
    have ha0 : a = 0 ∨ u = 0 := smul_eq_zero.1 h0
    cases hab with
    | inl hne =>
      cases ha0 with
      | inl ha0 => exact hne ha0
      | inr hu0 => exact hu hu0
    | inr hne => exact hne h
  -- step 5: solve for v:  v = (-a / b) • u
  have hvrel : v = (-a / b) • u := by
    have hstep : b • v = (-a) • u := by
      have hneg : b • v = -(a • u) := eq_neg_of_add_eq_zero_right hr
      simpa [neg_smul] using hneg
    calc
      v = (1 : K) • v := (one_smul (M := K) v).symm
      _ = (b⁻¹ * b) • v := by rw [← inv_mul_cancel₀ hb0]
      _ = b⁻¹ • (b • v) := by rw [mul_smul]
      _ = b⁻¹ • ((-a) • u) := by rw [hstep]
      _ = ((-a) / b) • u := by
        rw [← mul_smul, mul_comm, div_eq_mul_inv]
  -- step 6: c := -a / b has c ≠ 0 and c ≠ 1
  refine ⟨-a / b, ?_, ?_, hvrel⟩
  · by_contra h  -- h : -a / b = 0
    have h0 : a / b = 0 := by simpa using h
    have hab0 : a = 0 ∨ b = 0 := div_eq_zero_iff.1 h0
    cases hab0 with
    | inl ha0' => exact ha0 ha0'
    | inr hb0' => exact hb0 hb0'
  · by_contra h  -- h : -a / b = 1
    have h1 : v = (1 : K) • u := by simpa [h] using hvrel
    exact huv (by simpa [one_smul] using h1.symm)
end P2MHole01_ea06f50d

/-- Non-trivial dependence of a pair means one is a non-trivial scalar multiple of the other. -/
theorem cap42_dep_scalar (K : Type*) [Field K] {r : ℕ} (u v : Fin r → K)
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) (hn : ¬ LinearIndependent K ![u, v]) :
    ∃ c : K, c ≠ 0 ∧ c ≠ 1 ∧ v = c • u := by
  (first | exact P2MHole01_ea06f50d.solution K u v hu hv huv hn | (apply P2MHole01_ea06f50d.solution <;> assumption))

namespace P2MHole02_596970e2
universe u_1
theorem solution (K : Type u_1) [inst : Field K] {r : ℕ} (u v : Fin r → K) (c : K) (hc : c ≠ (0 : K))
  (hc1 : c ≠ (1 : K)) (h : v = c • u) : Collinear K {(0 : Fin r → K), u, v} := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  use (0 : Fin r → K), u
  intro p hp
  simp [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with (rfl | rfl | rfl)
  · use 0
    simp
  · use 1
    simp
  · use c
    rw [h]
    simp
end P2MHole02_596970e2

/-- A scalar multiple lies on the spanned line: {0, u, c•u} is collinear. -/
theorem cap42_collinear_scalar (K : Type*) [Field K] {r : ℕ} (u v : Fin r → K) (c : K)
    (hc : c ≠ 0) (hc1 : c ≠ 1) (h : v = c • u) :
    Collinear K ({0, u, v} : Set (Fin r → K)) := by
  (first | exact P2MHole02_596970e2.solution K u v c hc hc1 h | (apply P2MHole02_596970e2.solution <;> assumption))

namespace P2MHole03_6fc2af75
universe u_1
variable {K : Type u_1} [inst : Field K] {r : ℕ}

/-- The subtype of the two-point set `{x, y}` has cardinality `2` when `x ≠ y`. -/
lemma card_two (u : Submodule K (Fin r → K)) (x y : ↥u) (hxy : x ≠ y) :
    Cardinal.mk ↑({x, y} : Set ↥u) = 2 := by
  refine Cardinal.mk_eq_two_iff.mpr ⟨⟨x, by simp⟩, ⟨y, by simp⟩, ?_, ?_⟩
  · intro h
    exact hxy (Subtype.ext_iff.mp h)
  · ext z
    constructor
    · intro _
      exact Set.mem_univ z
    · intro _
      by_cases hx : z.1 = x
      · left
        exact Subtype.ext hx
      · by_cases hy : z.1 = y
        · right
          exact Subtype.ext hy
        · have hx2 : z.1 = x :=
            Set.eq_of_mem_insert_of_notMem z.2 (fun h2 => hy (by simpa using h2))
          left
          exact Subtype.ext hx2

/-- If `b ≠ c` and `![b, c]` is linearly independent in the ambient space, then the two
  points `b`, `c` are linearly independent on the submodule they span. -/
lemma pair_indep (b c : Fin r → K) (hb' : b ∈ Submodule.span K {b, c})
    (hc' : c ∈ Submodule.span K {b, c}) (hbc : b ≠ c) (hLI : LinearIndependent K ![b, c]) :
    LinearIndepOn K id
      ({(⟨b, hb'⟩ : ↥(Submodule.span K {b, c})), ⟨c, hc'⟩} : Set ↥(Submodule.span K {b, c})) := by
  let u := Submodule.span K {b, c}
  have hne : (⟨b, hb'⟩ : ↥u) ≠ (⟨c, hc'⟩ : ↥u) := fun h => hbc (Subtype.ext_iff.mp h)
  refine (LinearIndepOn.pair_iff id hne).mpr fun c₁ d h => by
    have h1 : c₁ • b + d • c = 0 := by simpa using h
    exact (LinearIndependent.pair_iff.mp hLI) c₁ d h1

theorem solution (K : Type u_1) [inst : Field K] {r : ℕ} (s : Set (Fin r → K)) (b c : Fin r → K)
  (hb : b ∈ s) (hc : c ∈ s) (h0 : (0 : Fin r → K) ∈ s) (hb0 : b ≠ (0 : Fin r → K)) (hc0 : c ≠ (0 : Fin r → K))
  (hbc : b ≠ c) (h : Collinear K s) : ¬LinearIndependent K ![b, c] := by
  intro hLI
  have hr : Module.rank K (vectorSpan K s) ≤ 1 := by
    simpa only [Collinear] using h
  have hspan : Submodule.span K {b, c} ≤ vectorSpan K s := by
    rw [vectorSpan]
    exact Submodule.span_mono (fun x hx => by
      rcases hx with rfl | rfl
      · rw [Set.mem_vsub]
        exact ⟨x, hb, 0, h0, by simp⟩
      · rw [Set.mem_vsub]
        exact ⟨x, hc, 0, h0, by simp⟩)
  have hr' : Module.rank K (Submodule.span K {b, c}) ≤ 1 :=
    (Submodule.rank_mono hspan).trans hr
  let u := Submodule.span K {b, c}
  have hb' : b ∈ u := Submodule.mem_span_of_mem (by simp)
  have hc' : c ∈ u := Submodule.mem_span_of_mem (by simp)
  have hne : (⟨b, hb'⟩ : ↥u) ≠ (⟨c, hc'⟩ : ↥u) := fun h => hbc (Subtype.ext_iff.mp h)
  have hrank2 : 2 ≤ Module.rank K u := by
    rw [le_rank_iff_exists_linearIndependent]
    refine ⟨{⟨b, hb'⟩, ⟨c, hc'⟩}, ?_, ?_⟩
    · exact card_two u ⟨b, hb'⟩ ⟨c, hc'⟩ hne
    · exact pair_indep b c hb' hc' hbc hLI
  exact lt_irrefl 2 (lt_of_le_of_lt (le_trans hrank2 hr') (by norm_num))
end P2MHole03_6fc2af75

/-- A line through 0 carrying two distinct non-zero points b, c forces b, c to be dependent. -/
theorem cap42_dep_pair_of0 (K : Type*) [Field K] {r : ℕ} (s : Set (Fin r → K))
    (b c : Fin r → K)
    (hb : b ∈ s) (hc : c ∈ s) (h0 : (0 : Fin r → K) ∈ s)
    (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hbc : b ≠ c)
    (h : Collinear K s) :
    ¬ LinearIndependent K ![b, c] := by
  (first | exact P2MHole03_6fc2af75.solution K s b c hb hc h0 hb0 hc0 hbc h | (apply P2MHole03_6fc2af75.solution <;> assumption))

namespace P2MHole04_f1f87fac
universe u_1
theorem solution (K : Type u_1) [inst : Field K] [inst_1 : Fintype K] (t : ℕ)
  (hK : Fintype.card K = (2 : ℕ) ^ t) : CharP K (2 : ℕ) := by
  exact charP_of_card_eq_prime_pow hK
end P2MHole04_f1f87fac

/-- `|K| = 2^t` implies `K` has characteristic 2. -/
theorem cap42_char2 (K : Type*) [Field K] [Fintype K] (t : ℕ)
    (hK : Fintype.card K = 2 ^ t) : CharP K 2 := by
  (first | exact P2MHole04_f1f87fac.solution K t hK | (apply P2MHole04_f1f87fac.solution <;> assumption))

namespace P2MHole05_12ba11f0
universe u_1
/-- In characteristic 2, `a + c = 0` forces `a = c` (because `-c = c`). -/
lemma char2_add_eq_zero_implies_eq {K : Type*} [Field K] (hchar : CharP K 2) {r : ℕ}
    (a c : Fin r → K) (h0 : a + c = 0) : a = c := by
  have ha : a = -c := by rwa [add_eq_zero_iff_eq_neg] at h0
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero (R := K) (p := 2)
  have hc_add_c : c + c = 0 := by rw [← two_smul (R := K), h2, zero_smul]
  have hcc : -c = c := (add_eq_zero_iff_eq_neg).mp hc_add_c |>.symm
  exact ha.trans hcc

/-- If `a + c = r₃ • v` and `b + c = (r₂ + r₃) • v` with `r₃ ≠ 0`, then `b + c`
is a scalar multiple of `a + c`. -/
lemma smul_multiple_of_common_dir {K : Type*} [Field K] {V : Type*} [AddCommMonoid V] [Module K V]
    (r₂ r₃ : K) (hr₃₀ : r₃ ≠ 0) (v a b c : V) (ha_c : a + c = r₃ • v) (hb_c : b + c = (r₂ + r₃) • v) :
    ∃ t : K, t • (a + c) = b + c := by
  use (r₂ + r₃) * r₃⁻¹
  calc
    ((r₂ + r₃) * r₃⁻¹) • (a + c) = ((r₂ + r₃) * r₃⁻¹) • (r₃ • v) := by rw [ha_c]
    _ = (((r₂ + r₃) * r₃⁻¹) * r₃) • v := by rw [← mul_smul]
    _ = (r₂ + r₃) • v := by rw [inv_mul_cancel_right₀ hr₃₀ (r₂ + r₃)]
    _ = b + c := hb_c.symm

theorem solution (K : Type u_1) [inst : Field K] [inst_1 : Fintype K] {r : ℕ} (hchar : CharP K (2 : ℕ))
  (a b c : Fin r → K) (ha0 : a ≠ (0 : Fin r → K)) (hb0 : b ≠ (0 : Fin r → K)) (hc0 : c ≠ (0 : Fin r → K)) (hab : a ≠ b)
  (hac : a ≠ c) (hbc : b ≠ c) (hcol : Collinear K {a, b, c}) : ¬LinearIndependent K ![a + c, b + c] := by
  -- a lies in the point set {a, b, c}
  have ha_mem : a ∈ ({a, b, c} : Set (Fin r → K)) := by simp
  -- Collinearity gives a one-parameter description of the points relative to a
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem ha_mem).mp hcol
  -- b and c are translations of a by multiples of a single direction v
  obtain ⟨r₂, hb⟩ := hv b (by simp)  -- hb : b = r₂•v +ᵥ a
  obtain ⟨r₃, hc⟩ := hv c (by simp)  -- hc : c = r₃•v +ᵥ a
  -- In the vector space, the affine +ᵥ is ordinary addition
  have hb' : b = a + r₂ • v := by simp [hb, vadd_eq_add, add_comm]
  have hc' : c = a + r₃ • v := by simp [hc, vadd_eq_add, add_comm]
  -- Characteristic two: (2 : K) = 0, hence a + a = 0
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero (R := K) (p := 2)
  have haa : a + a = 0 := by
    rw [← (two_smul (R := K) a), h2, zero_smul]
  -- a + c and b + c are both multiples of the single direction v
  have ha_c : a + c = r₃ • v := by
    calc
      a + c = a + (a + r₃ • v) := by rw [hc']
      _ = (a + a) + r₃ • v := by abel
      _ = 0 + r₃ • v := by rw [haa]
      _ = r₃ • v := by simp
  have hb_c : b + c = (r₂ + r₃) • v := by
    calc
      b + c = (a + r₂ • v) + (a + r₃ • v) := by rw [hb', hc']
      _ = (a + a) + (r₂ • v + r₃ • v) := by abel
      _ = 0 + (r₂ + r₃) • v := by rw [haa, add_smul]
      _ = (r₂ + r₃) • v := by simp
  -- r₃ ≠ 0, otherwise c = a
  have hr₃₀ : r₃ ≠ 0 := by
    intro hr3
    have : a = c := by rw [hc', hr3, zero_smul, add_zero]
    exact hac this
  -- a + c ≠ 0 (char 2: a + c = 0 iff a = c)
  have hne0 : a + c ≠ 0 := by
    intro h
    have : a = c := char2_add_eq_zero_implies_eq hchar a c h
    exact hac this
  -- b + c is a scalar multiple of a + c
  have hmult : ∃ t : K, t • (a + c) = b + c :=
    smul_multiple_of_common_dir r₂ r₃ hr₃₀ v a b c ha_c hb_c
  by_contra hli
  -- LinearIndependent of a pair (with first vector non-zero) iff the second is no multiple of the first
  rw [LinearIndependent.pair_iff' hne0] at hli
  obtain ⟨t, ht⟩ := hmult
  exact hli t ht
end P2MHole05_12ba11f0

-- riskiest
/-- In characteristic 2, a collinear triple of pairwise distinct non-zero points
  yields two non-zero distinct points of the form a + c, b + c that are dependent
  (via a = x•b + y•c with x + y = 1, x, y ≠ 0: a + c = x•(b + c), x ∉ {0, 1}). -/
theorem cap42_nonzero_case (K : Type*) [Field K] [Fintype K] {r : ℕ} (hchar : CharP K 2)
    (a b c : Fin r → K)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcol : Collinear K ({a, b, c} : Set (Fin r → K))) :
    ¬ LinearIndependent K ![(a + c), (b + c)] := by
  (first | exact P2MHole05_12ba11f0.solution K hchar a b c ha0 hb0 hc0 hab hac hbc hcol | (apply P2MHole05_12ba11f0.solution <;> assumption))

/-- In characteristic 2, a + c = 0 forces a = c. -/
theorem cap42_neg_self (K : Type*) [Field K] {r : ℕ} (hchar : CharP K 2)
    (a c : Fin r → K) (h : a + c = 0) : a = c := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hcc : c + c = 0 := by rw [← two_smul K c, htwo, zero_smul]
  exact (add_eq_zero_iff_eq_neg.mp h).trans ((add_eq_zero_iff_eq_neg.mp hcc).symm)

theorem solution (K : Type*) [Field K] [Fintype K] (t : ℕ)
    (hK : Fintype.card K = 2 ^ t) {r : ℕ} (G : AddSubgroup (Fin r → K)) :
    IsTranslationCap (KG G) ↔
      ∀ u ∈ G, ∀ v ∈ G, u ≠ 0 → v ≠ 0 → u ≠ v → LinearIndependent K ![u, v] := by
  refine ⟨fun HIs => fun u hu v hmv hu0 hv0 hne => ?_, fun Hlin => ?_⟩
  · -- (→) KG G is a cap
    obtain ⟨Hcap, -⟩ := HIs
    by_contra hdep
    obtain ⟨c, hc0, hc1, hcv⟩ := cap42_dep_scalar K u v hu0 hv0 hne hdep
    have hcoll : Collinear K ({0, u, v} : Set (Fin r → K)) :=
      cap42_collinear_scalar K u v c hc0 hc1 hcv
    exact (Hcap 0 (AddSubgroup.zero_mem G) u hu v hmv (Ne.symm hu0) (Ne.symm hv0) hne) hcoll
  · -- (←) KG G is a cap; the witness is G itself
    constructor
    · intro a ha b hb c hc hab hac hbc
      intro hcol
      have haG : a ∈ G := ha
      have hbG : b ∈ G := hb
      have hcG : c ∈ G := hc
      by_cases ha0 : a = 0
      · -- a = 0: b, c are the two non-zero distinct points on the line
        have hb0 : b ≠ 0 := fun h => hab (ha0.trans h.symm)
        have hc0 : c ≠ 0 := fun h => hac (ha0.trans h.symm)
        have hd : ¬ LinearIndependent K ![b, c] :=
          cap42_dep_pair_of0 K {a, b, c} b c (by simp) (by simp) (by simpa [ha0]) hb0 hc0 hbc hcol
        exact hd (Hlin b hb c hc hb0 hc0 hbc)
      · -- a ≠ 0
        by_cases hb0 : b = 0
        · -- b = 0: a, c are the two non-zero distinct points
          have ha0' : a ≠ 0 := ha0
          have hc0 : c ≠ 0 := fun h => hbc (hb0.trans h.symm)
          have hd : ¬ LinearIndependent K ![a, c] :=
            cap42_dep_pair_of0 K {a, b, c} a c (by simp) (by simp) (by simpa [hb0]) ha0' hc0 hac hcol
          exact hd (Hlin a ha c hc ha0' hc0 hac)
        · -- b ≠ 0
          by_cases hc0 : c = 0
          · -- c = 0: a, b are the two non-zero distinct points
            have ha0' : a ≠ 0 := ha0
            have hb0' : b ≠ 0 := hb0
            have hd : ¬ LinearIndependent K ![a, b] :=
              cap42_dep_pair_of0 K {a, b, c} a b (by simp) (by simp) (by simpa [hc0]) ha0' hb0' hab hcol
            exact hd (Hlin a ha b hb ha0' hb0' hab)
          · -- a, b, c all non-zero: shifts a+c, b+c are dependent
            have hch : CharP K 2 := cap42_char2 K t hK
            have hab0 : a + c ≠ 0 := fun h => hac (cap42_neg_self K hch a c h)
            have hbc0 : b + c ≠ 0 := fun h => hbc (cap42_neg_self K hch b c h)
            have hd : a + c ≠ b + c := fun h => hab ((add_left_inj c).mp h)
            have hdep : ¬ LinearIndependent K ![(a + c), (b + c)] :=
              cap42_nonzero_case K hch a b c ha0 hb0 hc0 hab hac hbc hcol
            exact hdep (Hlin (a + c) (AddSubgroup.add_mem G haG hcG) (b + c)
              (AddSubgroup.add_mem G hbG hcG) hab0 hbc0 hd)
    · exact ⟨G, rfl⟩
