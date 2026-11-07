-- Prove2me | solution 1 for SampleMechDesign.lemma_3_10
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T16:30:51.546932+00:00
-- url     : https://prove2.me/submissions/b64aa7ef-e5c3-421c-b3d5-e989cc98714a

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters
import Definitions.Def_SampleMechDesign_IsDelineable

set_option autoImplicit false

namespace SampleMechDesign.L310Aux

open Finset

/-- Sum of binomials up to `d` is at most `(n+1)^d`. -/
lemma sum_choose_le_pow (n d : ℕ) :
    ∑ k ∈ Iic d, n.choose k ≤ (n + 1) ^ d := by
  have hIic : Iic d = range (d + 1) := by
    ext k; simp
  calc ∑ k ∈ Iic d, n.choose k ≤ ∑ k ∈ Iic d, n ^ k * 1 ^ (d - k) * d.choose k := by
        apply Finset.sum_le_sum
        intro k hk
        have h1 : n.choose k ≤ n ^ k := Nat.choose_le_pow n k
        have h2 : 1 ≤ d.choose k := Nat.choose_pos (mem_Iic.1 hk)
        calc n.choose k ≤ n ^ k := h1
          _ = n ^ k * 1 ^ (d - k) * 1 := by simp
          _ ≤ n ^ k * 1 ^ (d - k) * d.choose k := Nat.mul_le_mul_left _ h2
    _ = (n + 1) ^ d := by rw [add_pow, hIic]; simp only [Nat.cast_id]

/-- Two reals with the same positivity of `x` and `-x` have the same sign. -/
lemma sign_eq_of {x y : ℝ} (h1 : 0 < x ↔ 0 < y) (h2 : 0 < -x ↔ 0 < -y) :
    SignType.sign x = SignType.sign y := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hy : y < 0 := by have := h2.1 (by linarith); linarith
    rw [sign_neg hx, sign_neg hy]
  · subst hx
    have hy1 : ¬ 0 < y := fun h => lt_irrefl _ (h1.2 h)
    have hy2 : ¬ 0 < -y := fun h => by have := h2.2 h; simp at this
    have hy : y = 0 := by push Not at hy1 hy2; linarith
    rw [hy]
  · have hy : 0 < y := h1.1 hx
    rw [sign_pos hx, sign_pos hy]

/-- **Dual VC bound for affine thresholds.** A family of subsets of a finite index set `ι`, each of
which is the positivity pattern `{j | 0 < w j ⬝ᵥ p + c j}` of some point `p ∈ ℝ^d`, has at most
`(|ι| + 1)^d` members: such a family shatters no set of more than `d` indices. -/
lemma card_pat_le {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (Q : Set (Fin d → ℝ))
    (w : ι → Fin d → ℝ) (c : ι → ℝ) (𝒜 : Finset (Finset ι))
    (h𝒜 : ∀ u ∈ 𝒜, ∃ p ∈ Q, ∀ j, j ∈ u ↔ 0 < w j ⬝ᵥ p + c j) :
    𝒜.card ≤ (Fintype.card ι + 1) ^ d := by
  classical
  have hshat : ∀ s : Finset ι, 𝒜.Shatters s → s.card ≤ d := by
    intro s hs
    by_contra hlt
    push Not at hlt
    have real : ∀ T ⊆ s, ∃ p ∈ Q, ∀ j ∈ s, (j ∈ T ↔ 0 < w j ⬝ᵥ p + c j) := by
      intro T hT
      obtain ⟨u, hu, hsu⟩ := hs hT
      obtain ⟨p, hpQ, hp⟩ := h𝒜 u hu
      refine ⟨p, hpQ, fun j hj => ?_⟩
      rw [← hsu, mem_inter, ← hp j]
      exact ⟨fun h => h.2, fun h => ⟨hj, h⟩⟩
    have hnli : ¬ LinearIndependent ℝ (fun j : s => w j) := by
      intro hli
      have := hli.fintype_card_le_finrank
      simp only [Fintype.card_coe, Module.finrank_fin_fun] at this
      omega
    obtain ⟨g, hg0, j0, hj0⟩ := Fintype.not_linearIndependent_iff.1 hnli
    let G : ι → ℝ := fun j => if h : j ∈ s then g ⟨j, h⟩ else 0
    have hGg : ∀ x : s, G x = g x := fun x => by simp [G, x.2]
    let ν : ℝ := ∑ j ∈ s, G j * c j
    have hrel0 : ∀ p : Fin d → ℝ, ∑ j ∈ s, G j * (w j ⬝ᵥ p + c j) = ν := by
      intro p
      have hw : ∑ j ∈ s, G j * (w j ⬝ᵥ p) = 0 := by
        have h1 : (∑ x : s, g x • w x) ⬝ᵥ p = 0 := by rw [hg0]; simp
        rw [sum_dotProduct] at h1
        simp only [smul_dotProduct, smul_eq_mul] at h1
        rw [← h1, ← Finset.sum_coe_sort s]
        exact Finset.sum_congr rfl (fun x _ => by rw [hGg])
      simp only [ν, mul_add, Finset.sum_add_distrib, hw, zero_add]
    -- the two contradiction patterns
    have Lpos : ∀ (H : ι → ℝ) (μ : ℝ), (∀ p, ∑ j ∈ s, H j * (w j ⬝ᵥ p + c j) = μ) → μ ≤ 0 →
        (∃ j ∈ s, 0 < H j) → False := by
      intro H μ hrel hμ ⟨j1, hj1s, hj1⟩
      obtain ⟨p, -, hp⟩ := real (s.filter (fun j => 0 < H j)) (filter_subset _ _)
      have hterm : ∀ j ∈ s, 0 ≤ H j * (w j ⬝ᵥ p + c j) := by
        intro j hj
        by_cases hH : 0 < H j
        · have := (hp j hj).1 (mem_filter.2 ⟨hj, hH⟩)
          positivity
        · have hF : ¬ 0 < w j ⬝ᵥ p + c j := fun h =>
            hH (mem_filter.1 ((hp j hj).2 h)).2
          push Not at hH hF
          exact mul_nonneg_of_nonpos_of_nonpos hH hF
      have hstrict : 0 < H j1 * (w j1 ⬝ᵥ p + c j1) :=
        mul_pos hj1 ((hp j1 hj1s).1 (mem_filter.2 ⟨hj1s, hj1⟩))
      have := Finset.sum_pos' hterm ⟨j1, hj1s, hstrict⟩
      rw [hrel p] at this
      linarith
    have L0 : ∀ (H : ι → ℝ) (μ : ℝ), (∀ p, ∑ j ∈ s, H j * (w j ⬝ᵥ p + c j) = μ) → μ < 0 →
        (∀ j ∈ s, H j ≤ 0) → False := by
      intro H μ hrel hμ hall
      obtain ⟨p, -, hp⟩ := real ∅ (empty_subset _)
      have hterm : ∀ j ∈ s, 0 ≤ H j * (w j ⬝ᵥ p + c j) := by
        intro j hj
        have hF : ¬ 0 < w j ⬝ᵥ p + c j := fun h => by simpa using (hp j hj).2 h
        push Not at hF
        exact mul_nonneg_of_nonpos_of_nonpos (hall j hj) hF
      have := Finset.sum_nonneg hterm
      rw [hrel p] at this
      linarith
    have hrelN : ∀ p, ∑ j ∈ s, (-G j) * (w j ⬝ᵥ p + c j) = -ν := by
      intro p
      simp only [neg_mul, Finset.sum_neg_distrib, hrel0 p]
    have hj0s : (j0 : ι) ∈ s := j0.2
    have hGj0 : G j0 ≠ 0 := by rw [hGg]; exact hj0
    rcases le_or_gt ν 0 with hν | hν
    · by_cases hex : ∃ j ∈ s, 0 < G j
      · exact Lpos G ν hrel0 hν hex
      · push Not at hex
        have hneg : G j0 < 0 := lt_of_le_of_ne (hex _ hj0s) hGj0
        rcases lt_or_eq_of_le hν with hν' | hν'
        · exact L0 G ν hrel0 hν' hex
        · exact Lpos (fun j => -G j) (-ν) hrelN (by rw [hν']; simp)
            ⟨j0, hj0s, by linarith⟩
    · by_cases hex : ∃ j ∈ s, 0 < -G j
      · exact Lpos (fun j => -G j) (-ν) hrelN (by linarith) hex
      · push Not at hex
        exact L0 (fun j => -G j) (-ν) hrelN (by linarith) hex
  have hvc : 𝒜.vcDim ≤ d := Finset.sup_le (fun s hs => hshat s (mem_shatterer.1 hs))
  calc 𝒜.card ≤ 𝒜.shatterer.card := card_le_card_shatterer 𝒜
    _ ≤ ∑ k ∈ Iic 𝒜.vcDim, (Fintype.card ι).choose k := card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Iic d, (Fintype.card ι).choose k :=
        Finset.sum_le_sum_of_subset (Iic_subset_Iic.2 hvc)
    _ ≤ (Fintype.card ι + 1) ^ d := sum_choose_le_pow _ _

/-- The real-number step: `2^m ≤ (6 m² t)^d` forces `m ≤ 9 d ln(4 d t)`. -/
lemma real_step {m d t : ℕ} (hd : 1 ≤ d) (ht : 1 ≤ t) (hm : 1 ≤ m)
    (h : (2 : ℝ) ^ m ≤ (6 * (m : ℝ) ^ 2 * t) ^ d) :
    (m : ℝ) ≤ 9 * (d : ℝ) * Real.log (4 * (d : ℝ) * (t : ℝ)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  set ℓ := Real.log 2 with hℓ
  have hℓ0 : 0.6931471803 < ℓ := Real.log_two_gt_d9
  have hLd : 0 ≤ Real.log d := Real.log_nonneg hd1
  have hLt : 0 ≤ Real.log t := Real.log_nonneg ht1
  -- take logs
  have hlog : (m : ℝ) * ℓ ≤ d * (Real.log 6 + 2 * Real.log m + Real.log t) := by
    have h1 := Real.log_le_log (by positivity) h
    rw [Real.log_pow, Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    push_cast at h1
    linarith
  have hlog6 : Real.log 6 ≤ 3 * ℓ := by
    have : Real.log 6 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
    have h8 : Real.log 8 = 3 * ℓ := by
      rw [hℓ, show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith
  have hlog9 : Real.log 9 ≤ 4 * ℓ := by
    have : Real.log 9 ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
    have h16 : Real.log 16 = 4 * ℓ := by
      rw [hℓ, show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    linarith
  -- log m ≤ m/(9d) - 1 + log 9 + log d
  have hlogm : Real.log m ≤ m / (9 * d) - 1 + Real.log 9 + Real.log d := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < m / (9 * d) by positivity)
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity)] at h1
    linarith
  have hmd : (m : ℝ) / (9 * d) * d = m / 9 := by field_simp
  have hkey : (m : ℝ) * (ℓ - 2 / 9) ≤ d * (11 * ℓ - 2 + Real.log t + 2 * Real.log d) := by
    have := mul_le_mul_of_nonneg_left hlogm hd0.le
    nlinarith
  have hL4 : Real.log (4 * (d : ℝ) * (t : ℝ)) = 2 * ℓ + Real.log d + Real.log t := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      hℓ, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [hL4]
  by_contra hcon
  push Not at hcon
  have hpos : 0 < ℓ - 2 / 9 := by linarith
  have h1 : 9 * d * (2 * ℓ + Real.log d + Real.log t) * (ℓ - 2 / 9) < (m : ℝ) * (ℓ - 2 / 9) :=
    mul_lt_mul_of_pos_right hcon hpos
  have h2 : d * (11 * ℓ - 2 + Real.log t + 2 * Real.log d) ≤
      9 * d * (2 * ℓ + Real.log d + Real.log t) * (ℓ - 2 / 9) := by
    have hq : 11 * ℓ - 2 ≤ 2 * ℓ * (9 * ℓ - 2) := by nlinarith
    have hc : 2 ≤ 9 * ℓ - 2 := by linarith
    have e : 9 * d * (2 * ℓ + Real.log d + Real.log t) * (ℓ - 2 / 9) =
        d * (2 * ℓ * (9 * ℓ - 2) + (9 * ℓ - 2) * Real.log d + (9 * ℓ - 2) * Real.log t) := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ hd0.le
    nlinarith
  linarith

end SampleMechDesign.L310Aux

open SampleMechDesign FoundationsML.Regression in
theorem solution {X : Type*} {d t : ℕ} (hd : 1 ≤ d) (ht : 1 ≤ t) {P : Set (Fin d → ℝ)}
    {profit : (Fin d → ℝ) → X → ℝ} (hdel : IsDelineable d t P profit)
    {m : ℕ} (z : Fin m → X) (hz : Shatters (profit '' P) z) :
    (m : ℝ) ≤ 9 * (d : ℝ) * Real.log (4 * (d : ℝ) * (t : ℝ)) := by
  classical
  obtain ⟨r, hr⟩ := hz
  have hex : ∀ b : Fin m → Bool, ∃ p ∈ P, ∀ i, b i ↔ r i < profit p (z i) := by
    intro b
    obtain ⟨g, ⟨p, hp, rfl⟩, h⟩ := hr b
    exact ⟨p, hp, h⟩
  choose pb hpbP hpb using hex
  choose H hHcard _hH0 hHaff using fun i => hdel (z i)
  choose A B hAB using hHaff
  let U : Finset ((Fin d → ℝ) × ℝ) := Finset.univ.biUnion H
  let w1 : ↥U × Bool → Fin d → ℝ := fun j => if j.2 then j.1.1.1 else -j.1.1.1
  let c1 : ↥U × Bool → ℝ := fun j => if j.2 then -j.1.1.2 else j.1.1.2
  let κ : (Fin d → ℝ) → Finset (↥U × Bool) := fun p =>
    Finset.univ.filter (fun j => 0 < w1 j ⬝ᵥ p + c1 j)
  let T1 := (Finset.univ : Finset (Fin m → Bool)).image (fun b => κ (pb b))
  have hT1 : T1.card ≤ (Fintype.card (↥U × Bool) + 1) ^ d := by
    apply SampleMechDesign.L310Aux.card_pat_le P w1 c1 T1
    intro u hu
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hu
    exact ⟨pb b, hpbP b, fun j => by simp [κ]⟩
  have hfib : ∀ k ∈ T1,
      ((Finset.univ : Finset (Fin m → Bool)).filter (fun b => κ (pb b) = k)).card ≤
        (m + 1) ^ d := by
    intro k hk
    obtain ⟨b0, -, hb0⟩ := Finset.mem_image.1 hk
    let σ : (Fin d → ℝ) × ℝ → SignType := fun h => SignType.sign (h.1 ⬝ᵥ pb b0 - h.2)
    let w2 : Fin m → Fin d → ℝ := fun i => A i σ
    let c2 : Fin m → ℝ := fun i => B i σ - r i
    let φ : (Fin m → Bool) → Finset (Fin m) := fun b => Finset.univ.filter (fun i => b i = true)
    have hφ : Function.Injective φ := by
      intro b b' hbb
      funext i
      have := congrArg (fun s => i ∈ s) hbb
      simp only [φ, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
      cases hb : b i <;> cases hb' : b' i <;> simp_all
    set F := (Finset.univ : Finset (Fin m → Bool)).filter (fun b => κ (pb b) = k) with hF
    rw [← Finset.card_image_of_injective F hφ, show m + 1 = Fintype.card (Fin m) + 1 by simp]
    apply SampleMechDesign.L310Aux.card_pat_le P w2 c2
    intro u hu
    obtain ⟨b, hbF, rfl⟩ := Finset.mem_image.1 hu
    have hbk : κ (pb b) = κ (pb b0) := by
      rw [hb0]; exact (Finset.mem_filter.1 hbF).2
    refine ⟨pb b, hpbP b, fun i => ?_⟩
    have hsgn : ∀ h ∈ H i, SignType.sign (h.1 ⬝ᵥ pb b - h.2) = σ h := by
      intro h hh
      have hU : h ∈ U := Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hh⟩
      have e1 := congrArg (fun s => ((⟨h, hU⟩ : ↥U), true) ∈ s) hbk
      have e2 := congrArg (fun s => ((⟨h, hU⟩ : ↥U), false) ∈ s) hbk
      simp only [κ, w1, c1, Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff,
        if_true, Bool.false_eq_true, if_false, neg_dotProduct] at e1 e2
      apply SampleMechDesign.L310Aux.sign_eq_of
      · constructor
        · intro hx; have := e1.1 (by linarith); linarith
        · intro hx; have := e1.2 (by linarith); linarith
      · constructor
        · intro hx; have := e2.1 (by linarith); linarith
        · intro hx; have := e2.2 (by linarith); linarith
    have hprof := hAB i σ (pb b) (hpbP b) hsgn
    have hbi := hpb b i
    simp only [φ, Finset.mem_filter, Finset.mem_univ, true_and, w2, c2]
    rw [hbi, hprof]
    constructor <;> intro hh <;> linarith
  have hcount : Fintype.card (Fin m → Bool) ≤
      (m + 1) ^ d * (Fintype.card (↥U × Bool) + 1) ^ d := by
    have h1 := Finset.card_le_mul_card_image (Finset.univ : Finset (Fin m → Bool)) _ hfib
    rw [Finset.card_univ] at h1
    exact h1.trans (Nat.mul_le_mul_left _ hT1)
  have hUcard : U.card ≤ m * t := by
    calc U.card ≤ ∑ i, (H i).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin m, t := Finset.sum_le_sum (fun i _ => hHcard i)
      _ = m * t := by simp
  have hcardι : Fintype.card (↥U × Bool) ≤ 2 * m * t := by
    rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_bool]
    nlinarith
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcount
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [Nat.cast_zero]
    have : (0 : ℝ) ≤ Real.log (4 * (d : ℝ) * (t : ℝ)) := by
      apply Real.log_nonneg
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
      nlinarith
    positivity
  · apply SampleMechDesign.L310Aux.real_step hd ht hm
    have hnat : 2 ^ m ≤ (6 * m ^ 2 * t) ^ d := by
      refine hcount.trans ?_
      rw [← mul_pow]
      apply Nat.pow_le_pow_left
      have h1 : (m + 1) ≤ 2 * m := by omega
      have h2 : Fintype.card (↥U × Bool) + 1 ≤ 3 * m * t := by
        have : 1 ≤ m * t := Nat.one_le_iff_ne_zero.2 (by positivity)
        nlinarith
      calc (m + 1) * (Fintype.card (↥U × Bool) + 1) ≤ (2 * m) * (3 * m * t) :=
            Nat.mul_le_mul h1 h2
        _ = 6 * m ^ 2 * t := by ring
    exact_mod_cast hnat
