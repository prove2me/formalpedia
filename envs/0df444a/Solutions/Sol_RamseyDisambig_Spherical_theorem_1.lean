-- Prove2me | solution 1 for RamseyDisambig.Spherical.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:03:10.5938+00:00
-- url     : https://prove2.me/submissions/466f3f48-2f74-4530-af9f-7fcda3e88bfe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RamseyDisambig_Spherical_GapColoring
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_RamseyDisambig_Spherical_Sphere
import Theorems.Thm_RamseyDisambig_Spherical_theorem_2
import Theorems.Thm_RamseyDisambig_Spherical_lemma_10

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.Basics

open RamseyDisambig.Spherical NatureSLT.GrowthFunction

/-- If `q ≤ vcDim Q` then some `q` points are shattered. -/
theorem exists_shattered_of_le_vcDim {Z Λ : Type*} (Q : Λ → Z → Bool) (q : ℕ) (hq1 : 1 ≤ q)
    (h : (q : ℕ∞) ≤ vcDim Q) : ∃ z : Fin q → Z, Shatters Q z := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ (h' : ℕ), (∃ z : Fin h' → Z, Shatters Q z) → h' < q := by
    intro h' ⟨z, hz⟩
    by_contra hlt
    push_neg at hlt
    apply hcon (fun i => z (Fin.castLE hlt i))
    intro δ
    obtain ⟨α, hα⟩ := hz (fun j => if hj : (j : ℕ) < q then δ ⟨j, hj⟩ else false)
    refine ⟨α, fun i => ?_⟩
    have := hα (Fin.castLE hlt i)
    simpa using this
  have hle : vcDim Q ≤ ((q - 1 : ℕ) : ℕ∞) := by
    unfold vcDim
    refine iSup₂_le fun h' hh' => ?_
    have := key h' hh'
    exact_mod_cast Nat.le_sub_one_of_lt this
  have hq : (q : ℕ∞) ≤ ((q - 1 : ℕ) : ℕ∞) := h.trans hle
  have hq' : q ≤ q - 1 := by exact_mod_cast hq
  omega

end RamseyDisambig.Dev.Basics
end

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.Thm1

open RamseyDisambig.Spherical NatureSLT.GrowthFunction

noncomputable section

/-- Sign of a Boolean coordinate. -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

lemma sgn_mul (a b : Bool) : sgn a * sgn b = 1 - 2 * (if a ≠ b then 1 else 0) := by
  cases a <;> cases b <;> simp [sgn] <;> norm_num

def phiVec (n : ℕ) (x : Fin n → Bool) : EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm (fun i => sgn (x i) / Real.sqrt n)

lemma phiVec_apply (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    phiVec n x i = sgn (x i) / Real.sqrt n := rfl

lemma phiVec_inner (n : ℕ) (hn : 1 ≤ n) (x y : Fin n → Bool) :
    inner ℝ (phiVec n x) (phiVec n y) = 1 - 2 * (hammingDist x y : ℝ) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn'.le
  have hsq : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn').ne'
  rw [PiLp.inner_apply]
  have : ∀ i, inner ℝ (phiVec n x i) (phiVec n y i)
      = (1 - 2 * (if x i ≠ y i then 1 else 0)) / n := by
    intro i
    rw [phiVec_apply, phiVec_apply, real_inner_eq_re_inner]
    simp only [RCLike.inner_apply, conj_trivial]
    rw [mul_comm]
    rw [div_mul_div_comm, ← sgn_mul, hs]
    simp
  simp only [this]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h2 : (∑ i, (if x i ≠ y i then (1:ℝ) else 0)) = (hammingDist x y : ℝ) := by
    rw [hammingDist, Finset.card_filter]; push_cast; rfl
  rw [h2]; simp; field_simp

lemma phiVec_norm (n : ℕ) (hn : 1 ≤ n) (x : Fin n → Bool) : ‖phiVec n x‖ = 1 := by
  have h := phiVec_inner n hn x x
  rw [real_inner_self_eq_norm_sq] at h
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp at h
  have h0 := norm_nonneg (phiVec n x)
  rcases h with h | h
  · exact h
  · linarith

def phi (d : ℕ) (x : Cube (d+1)) : Sphere d :=
  ⟨phiVec (d+1) x, by simpa using phiVec_norm (d+1) (by omega) x⟩

lemma angle_phi (d : ℕ) (x y : Cube (d+1)) :
    sphericalDistance (phi d x) (phi d y)
      = Real.arccos (1 - 2 * (hammingDist x y : ℝ) / (d+1 : ℕ)) := by
  unfold sphericalDistance InnerProductGeometry.angle phi
  simp only
  rw [phiVec_norm _ (by omega), phiVec_norm _ (by omega), phiVec_inner _ (by omega)]
  simp

theorem part_a (ε : ℝ) (h0 : 0 < ε) (hπ : ε < Real.pi / 2) (k : ℕ) :
    ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
      ∀ c : Sphere d → Sphere d → Bool, IsSphericalDisambiguation ε d c →
        (k : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim c := by
  have hcos0 : 0 < Real.cos ε := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hπ⟩
  have hcos1 : Real.cos ε < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (le_refl 0) hπ.le h0
    simpa using this
  set η : ℝ := (1 - Real.cos ε) / 2 with hη
  obtain ⟨N₀, hN₀, hN⟩ := theorem_2 η (by rw [hη]; linarith) (by rw [hη]; linarith) k
  refine ⟨N₀, hN₀, fun d hd c hc => ?_⟩
  have hdis : IsGapHammingDisambiguation η (d+1) (fun x y => c (phi d x) (phi d y)) := by
    intro x y b hb
    have hang := angle_phi d x y
    have hn : (0:ℝ) < ((d+1 : ℕ) : ℝ) := by positivity
    unfold gapHammingMatrix cubeDistance at hb
    split_ifs at hb with h1 h2
    · have hb' : b = false := by simpa using hb.symm
      subst hb'
      apply hc
      have : sphericalDistance (phi d x) (phi d y) ≤ ε := by
        rw [hang]
        calc Real.arccos (1 - 2 * (hammingDist x y : ℝ) / (d+1 : ℕ))
            ≤ Real.arccos (Real.cos ε) := by
              apply Real.arccos_le_arccos
              rw [hη] at h1
              have : 2 * (hammingDist x y : ℝ) / ((d+1 : ℕ):ℝ) ≤ 1 - Real.cos ε := by
                rw [div_le_iff₀ hn]; linarith
              linarith
          _ = ε := Real.arccos_cos h0.le (by linarith [Real.pi_pos])
      simp [sphericalMarginMatrix, this]
    · have hb' : b = true := by simpa using hb.symm
      subst hb'
      apply hc
      have : Real.pi - ε ≤ sphericalDistance (phi d x) (phi d y) := by
        rw [hang]
        calc Real.pi - ε = Real.arccos (-Real.cos ε) := by
              rw [Real.arccos_neg, Real.arccos_cos h0.le (by linarith [Real.pi_pos])]
          _ ≤ _ := by
              apply Real.arccos_le_arccos
              rw [hη] at h2
              have : 1 + Real.cos ε ≤ 2 * (hammingDist x y : ℝ) / ((d+1 : ℕ):ℝ) := by
                rw [le_div_iff₀ hn]; nlinarith
              linarith
      have hn2 : ¬ sphericalDistance (phi d x) (phi d y) ≤ ε := by
        intro h; linarith
      simp [sphericalMarginMatrix, hn2, this]
  have h1 := hN (d+1) (by omega) _ hdis
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  exact lemma_10 (phi d) (phi d) c k hk h1

theorem part_b (ε : ℝ) (h0 : 0 < ε) (hπ : ε < Real.pi / 2) : SphericalFamilyUniversal ε := by
  intro a b F
  rcases Nat.eq_zero_or_pos (a + b) with hab | hK
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha; subst hb
    refine ⟨1, fun c _ => ?_⟩
    exact ⟨fun i => i.elim0, fun j => j.elim0, fun i => i.elim0, fun j => j.elim0,
      fun i => i.elim0⟩
  obtain ⟨d₀, hd₀, hd⟩ := part_a ε h0 hπ (a + b)
  refine ⟨⟨max d₀ 1, by omega⟩, fun c hc => ?_⟩
  have hvc := hd (max d₀ 1) (le_max_left _ _) c hc
  obtain ⟨z, hz⟩ := RamseyDisambig.Dev.Basics.exists_shattered_of_le_vcDim c (a + b) hK hvc
  let δ : Fin a → Fin (a + b) → Bool := fun i =>
    Fin.append (fun i' : Fin a => decide (i = i')) (fun j => F i j)
  choose ρ hρ using fun i => hz (δ i)
  have hzinj : Function.Injective z := by
    intro p q hpq
    obtain ⟨α, hα⟩ := hz (fun r => decide (r = p))
    have h1 := hα p
    have h2 := hα q
    rw [← hpq, h1] at h2
    exact (by simpa using h2 : q = p).symm
  refine ⟨ρ, fun j => z (Fin.natAdd a j), ?_, ?_, ?_⟩
  · intro i i' h
    have h1 := hρ i (Fin.castAdd b i)
    have h2 := hρ i' (Fin.castAdd b i)
    rw [h] at h1
    rw [h1] at h2
    simp [δ] at h2
    exact h2.symm
  · intro j j' h
    exact Fin.ext (by simpa using congrArg Fin.val (hzinj h))
  · intro i j
    have := hρ i (Fin.natAdd a j)
    simpa [δ] using this

end

end RamseyDisambig.Dev.Thm1

namespace RamseyDisambig.Spherical

theorem chk_theorem_1 :
    (∀ ε : ℝ, 0 < ε → ε < Real.pi / 2 → ∀ k : ℕ,
      ∃ d₀ : ℕ, 1 ≤ d₀ ∧ ∀ d : ℕ, d₀ ≤ d →
        ∀ c : Sphere d → Sphere d → Bool, IsSphericalDisambiguation ε d c →
          (k : ℕ∞) ≤ NatureSLT.GrowthFunction.vcDim c) ∧
    (∀ ε : ℝ, 0 < ε → ε < Real.pi / 2 → SphericalFamilyUniversal ε) :=
  ⟨fun ε h0 hπ k => RamseyDisambig.Dev.Thm1.part_a ε h0 hπ k,
   fun ε h0 hπ => RamseyDisambig.Dev.Thm1.part_b ε h0 hπ⟩

end RamseyDisambig.Spherical
end

theorem solution : type_of% @RamseyDisambig.Spherical.chk_theorem_1 := @RamseyDisambig.Spherical.chk_theorem_1
