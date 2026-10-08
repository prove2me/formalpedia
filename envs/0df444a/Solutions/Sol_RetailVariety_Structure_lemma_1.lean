-- Prove2me | solution 1 for RetailVariety.Structure.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:05:06.022993+00:00
-- url     : https://prove2.me/submissions/63454461-8db5-40c8-a386-8337547672b1

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
open RetailVariety.Structure

private lemma power_identity (x D β : ℝ) (hx : 0 ≤ x) (hD : 0 < D) :
    D * (x/D)^β = x^β * D^(1-β) := by
  rw [Real.div_rpow hx hD.le, Real.rpow_sub hD, Real.rpow_one]
  ring

private lemma perspective (K β : ℝ) (hK : 0 < K) (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => x^β*(K+x)^(1-β)) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_Ici] at hx hy
  let z := a*x+b*y
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hDx : 0 < K+x := by linarith
  have hDy : 0 < K+y := by linarith
  have hDz : 0 < K+z := by linarith
  have he : a*(K+x)+b*(K+y) = K+z := by dsimp [z]; nlinarith [hab]
  let A := a*(K+x)/(K+z)
  let B := b*(K+y)/(K+z)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hAB : A+B=1 := by dsimp [A,B]; rw [← add_div, he, div_self hDz.ne']
  have hxy : A*(x/(K+x))+B*(y/(K+y)) = z/(K+z) := by
    dsimp [A,B,z]; field_simp; <;> ring
  have hh := (Real.concaveOn_rpow hβ hβ1).2 (div_nonneg hx hDx.le)
    (div_nonneg hy hDy.le) hA hB hAB
  simp only [smul_eq_mul, hxy] at hh
  have ht := mul_le_mul_of_nonneg_left hh hDz.le
  have hax : (K+z)*A = a*(K+x) := by dsimp [A]; field_simp
  have hby : (K+z)*B = b*(K+y) := by dsimp [B]; field_simp
  rw [mul_add, ← mul_assoc, ← mul_assoc, hax, hby, mul_assoc, mul_assoc,
    power_identity x (K+x) β hx hDx, power_identity y (K+y) β hy hDy,
    power_identity z (K+z) β hz hDz] at ht
  simpa [smul_eq_mul, z, mul_comm, add_assoc] using ht

private lemma affine (K : ℝ) (D : Set ℝ) (hD : Convex ℝ D) :
    ConvexOn ℝ D (fun x : ℝ => K+x) ∧ ConcaveOn ℝ D (fun x : ℝ => K+x) := by
  constructor <;> refine ⟨hD, ?_⟩ <;> intro x hx y hy a b ha hb hab <;>
    simp only [smul_eq_mul] <;> nlinarith [congrArg (fun t : ℝ => t*K) hab]

private lemma convex_max_zero {D : Set ℝ} {f : ℝ → ℝ} (hf : ConvexOn ℝ D f) :
    ConvexOn ℝ D (fun x => max (f x) 0) := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hh := hf.2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  apply max_le
  · have h1 := mul_le_mul_of_nonneg_left (le_max_left (f x) 0) ha
    have h2 := mul_le_mul_of_nonneg_left (le_max_left (f y) 0) hb
    linarith
  · positivity

theorem convex_pair (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (hanti : Antitone v) (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p)
    (hlam : 0 < lam) (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (S : Finset (Fin n)) :
    ConvexOn ℝ (Set.Icc 0 (v ⟨0, hn⟩)) (gI p c lam σ β v v0 S) ∧
      ConvexOn ℝ (Set.Icc 0 (v ⟨0, hn⟩)) (gT p c lam v v0 S) := by
  let D := Set.Icc 0 (v ⟨0,hn⟩)
  let K := ∑ j ∈ S, v j + v0
  have hK : 0 < K := add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun j _ => (hv j).le) hv0
  have hsub : D ⊆ Set.Ici 0 := fun _ hx => hx.1
  have hf : ConcaveOn ℝ D (fun x : ℝ => (K+x)^(1-β)) := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh := (Real.concaveOn_rpow (by linarith : 0 ≤ 1-β) (by linarith : 1-β ≤ 1)).2
      (show 0 ≤ K+x by linarith [hx.1]) (show 0 ≤ K+y by linarith [hy.1]) ha hb hab
    have he : a*(K+x)+b*(K+y) = K+(a*x+b*y) := by
      nlinarith [congrArg (fun t : ℝ => t*K) hab]
    simpa only [smul_eq_mul, he] using hh
  have hp := (perspective K β hK hβ0 hβ1.le).subset hsub (convex_Icc _ _)
  have hsum : ConcaveOn ℝ D (fun x : ℝ => (∑ j ∈ S, v j^β)*(K+x)^(1-β)+x^β*(K+x)^(1-β)) :=
    (hf.smul (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (hv j).le β)).add hp
  have hcoef : 0 ≤ p*σ*lam^β*Real.exp (-(criticalFractile p c)^2/2)/Real.sqrt (2*Real.pi) := by
    have hpp : 0 < p := lt_trans hc hcp
    positivity
  constructor
  · have hlin := ((affine (∑ j ∈ S, v j) D (convex_Icc _ _)).1).smul
      (show 0 ≤ (p-c)*lam by positivity)
    have hh := hlin.sub (hsum.smul hcoef)
    have he : gI p c lam σ β v v0 S =
        (fun x : ℝ => (p-c)*lam*(∑ j ∈ S, v j+x) -
          (p*σ*lam^β*Real.exp (-(criticalFractile p c)^2/2)/Real.sqrt (2*Real.pi))*
          ((∑ j ∈ S, v j^β)*(K+x)^(1-β)+x^β*(K+x)^(1-β))) := by
      funext x
      dsimp [gI, fDen, K]
      ring
    rw [he]
    exact hh
  · have ha (j : Fin n) : ConvexOn ℝ D (fun x : ℝ => p*v j-c*(K+x)) := by
      refine ⟨convex_Icc _ _, ?_⟩
      intro x hx y hy a b ha hb hab
      simp only [smul_eq_mul]
      nlinarith [congrArg (fun t : ℝ => t*(p*v j-c*K)) hab]
    have hb : ConvexOn ℝ D (fun x : ℝ => p*x-c*(K+x)) := by
      refine ⟨convex_Icc _ _, ?_⟩
      intro x hx y hy a b ha hb hab
      simp only [smul_eq_mul]
      nlinarith [congrArg (fun t : ℝ => t*(c*K)) hab]
    have hs (T : Finset (Fin n)) : ConvexOn ℝ D (fun x : ℝ => ∑ j ∈ T, max (p*v j-c*(K+x)) 0) := by
      classical
      induction T using Finset.induction_on with
      | empty => simpa using (convexOn_const (0 : ℝ) (convex_Icc 0 (v ⟨0,hn⟩)))
      | @insert j S hj ih =>
        have ht := (convex_max_zero (ha j)).add ih
        refine ⟨ht.1, ?_⟩
        intro x hx y hy a b ha hb hab
        simpa only [Finset.sum_insert hj, Pi.add_apply, smul_eq_mul] using ht.2 hx hy ha hb hab
    have hh := ((hs S).add
      (convex_max_zero hb)).smul hlam.le
    apply hh.congr
    intro x hx
    simp [gT, fDen, K, smul_eq_mul, add_assoc, add_comm, add_left_comm]

private theorem ratio {E : Type*} [AddCommGroup E] [Module ℝ E] (X : Set E)
    (g f : E → ℝ) (hg : ConvexOn ℝ X g) (hf_pos : ∀ x ∈ X, 0 < f x)
    (hf_lin : ConvexOn ℝ X f ∧ ConcaveOn ℝ X f) :
    QuasiconvexOn ℝ X (fun x => g x / f x) := by
  intro r
  intro x hx y hy a b ha hb hab
  have hz := hg.1 hx.1 hy.1 ha hb hab
  refine ⟨hz, ?_⟩
  have hfx := hf_pos x hx.1
  have hfy := hf_pos y hy.1
  have hxy := hg.2 hx.1 hy.1 ha hb hab
  have hf1 := hf_lin.1.2 hx.1 hy.1 ha hb hab
  have hf2 := hf_lin.2.2 hx.1 hy.1 ha hb hab
  have he : f (a • x + b • y) = a * f x + b * f y := by
    simpa only [smul_eq_mul] using le_antisymm hf1 hf2
  have hx' := (div_le_iff₀ hfx).mp hx.2
  have hy' := (div_le_iff₀ hfy).mp hy.2
  apply (div_le_iff₀ (hf_pos _ hz)).mpr
  rw [he]
  have hax := mul_le_mul_of_nonneg_left hx' ha
  have hby := mul_le_mul_of_nonneg_left hy' hb
  simp only [smul_eq_mul] at hxy
  nlinarith

theorem solution (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (hanti : Antitone v) (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p)
    (hlam : 0 < lam) (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (S : Finset (Fin n)) :
    QuasiconvexOn ℝ (Set.Icc 0 (v ⟨0, hn⟩)) (hI p c lam σ β v v0 S) ∧
      QuasiconvexOn ℝ (Set.Icc 0 (v ⟨0, hn⟩)) (hT p c lam v v0 S) := by
  have hg := convex_pair n hn v v0 hv hv0 hanti p c lam σ β hc hcp hlam hσ hβ0 hβ1 S
  have hp : ∀ x ∈ Set.Icc 0 (v ⟨0,hn⟩), 0 < fDen v v0 S x := by
    intro x hx
    dsimp [fDen]
    have hs := Finset.sum_nonneg (fun j (_ : j ∈ S) => (hv j).le)
    linarith [hx.1]
  have hf : ConvexOn ℝ (Set.Icc 0 (v ⟨0,hn⟩)) (fDen v v0 S) ∧ ConcaveOn ℝ (Set.Icc 0 (v ⟨0,hn⟩)) (fDen v v0 S) := by
    have ht := affine (∑ j ∈ S, v j+v0) (Set.Icc 0 (v ⟨0,hn⟩)) (convex_Icc _ _)
    exact ⟨ht.1.congr (by intro x hx; dsimp [fDen]; ring),
      ht.2.congr (by intro x hx; dsimp [fDen]; ring)⟩
  exact ⟨ratio _ _ _ hg.1 hp hf, ratio _ _ _ hg.2 hp hf⟩


#print axioms solution
