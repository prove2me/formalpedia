-- Prove2me | solution 1 for RetailVariety.Structure.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T22:02:38.677125+00:00
-- url     : https://prove2.me/submissions/98c36c84-53e9-49c4-baa4-19f5aec60b15

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

private theorem qc_pair (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
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





private lemma den_pos {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (S : Finset (Fin n)) : 0 < ∑ j ∈ S, v j + v0 := by
  exact add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun j _ => (hv j).le) hv0

private lemma independent {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (p c lam σ β : ℝ) (S : Finset (Fin n)) :
    profitI p c lam σ β v v0 S =
      ((p-c)*lam*(∑ j ∈ S, v j) -
        (p*σ*lam^β*Real.exp (-(criticalFractile p c)^2/2)/Real.sqrt (2*Real.pi))*
        (∑ j ∈ S, v j^β)*(∑ j ∈ S, v j+v0)^(1-β)) / (∑ j ∈ S, v j+v0) := by
  have hD := den_pos v v0 hv hv0 S
  have hp : (∑ j ∈ S, v j+v0)^(1-β) / (∑ j ∈ S, v j+v0) =
      1 / (∑ j ∈ S, v j+v0)^β := by
    rw [Real.rpow_sub hD, Real.rpow_one]
    field_simp
  unfold profitI share
  simp_rw [Real.div_rpow (hv _).le hD.le]
  rw [← Finset.sum_div, ← Finset.sum_div, sub_div]
  simp only [mul_div_assoc]
  rw [hp]
  ring

private lemma trend {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (p c lam : ℝ) (S : Finset (Fin n)) :
    profitT p c lam v v0 S =
      lam * (∑ j ∈ S, max (p*v j-c*(∑ i ∈ S, v i+v0)) 0) / (∑ i ∈ S, v i+v0) := by
  have hD := den_pos v v0 hv hv0 S
  unfold profitT share
  have he (j : Fin n) : p * (v j / (∑ i ∈ S, v i+v0)) - c =
      (p*v j-c*(∑ i ∈ S, v i+v0))/(∑ i ∈ S, v i+v0) := by field_simp
  have hm (z : ℝ) : max (z / (∑ i ∈ S, v i+v0)) 0 =
      max z 0 / (∑ i ∈ S, v i+v0) := by
    simpa using (max_div_div_right hD.le z 0)
  simp_rw [he, hm]
  rw [← Finset.sum_mul, ← Finset.sum_div]
  ring

private theorem endpoints {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j) (hv0 : 0 < v0)
    (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam) (hσ : 0 < σ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (S : Finset (Fin n)) :
    (∀ j, j ∉ S → hI p c lam σ β v v0 S (v j) = profitI p c lam σ β v v0 (insert j S)) ∧
      (∀ j, j ∉ S → hT p c lam v v0 S (v j) = profitT p c lam v v0 (insert j S)) ∧
      hT p c lam v v0 S 0 = profitT p c lam v v0 S ∧
      (0 < β → hI p c lam σ β v v0 S 0 = profitI p c lam σ β v v0 S) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [independent v v0 hv hv0]
    simp [hI, gI, fDen, Finset.sum_insert, hj, add_comm]
  · intro j hj
    rw [trend v v0 hv hv0]
    simp [hT, gT, fDen, Finset.sum_insert, hj, add_comm]
  · rw [trend v v0 hv hv0]
    have hD := den_pos v v0 hv hv0 S
    have hm : max (-(c*(∑ j ∈ S, v j+v0))) 0 = 0 := max_eq_right (by nlinarith)
    simp [hT, gT, fDen, hm]
  · intro hb
    rw [independent v v0 hv hv0]
    simp [hI, gI, fDen, Real.zero_rpow hb.ne']



set_option autoImplicit false

private def rank {n : ℕ} (S : Finset (Fin n)) : ℕ := ∑ j ∈ S, (j.val+1)

private lemma rank_erase {n : ℕ} (S : Finset (Fin n)) (k : Fin n) (hk : k ∈ S) :
    rank (S.erase k) < rank S := by
  have he := Finset.sum_erase_add S (fun j : Fin n => j.val+1) hk
  unfold rank
  omega

private lemma prefix_dom {n : ℕ} (F : Finset (Fin n) → ℝ)
    (hgap : ∀ S (j k : Fin n), j < k → j ∉ S → k ∈ S →
      F S ≤ max (F (S.erase k)) (F (insert j (S.erase k)))) (S : Finset (Fin n)) :
    ∃ i : ℕ, i ≤ n ∧ F S ≤ F (popularSet n i) := by
  classical
  suffices hh : ∀ r S, rank S = r → ∃ i, i ≤ n ∧ F S ≤ F (popularSet n i) from hh _ S rfl
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro S hr
    by_cases hg : ∃ j k : Fin n, j < k ∧ j ∉ S ∧ k ∈ S
    · obtain ⟨j,k,hjk,hj,hk⟩ := hg
      have hT := rank_erase S k hk
      have hjT : j ∉ S.erase k := fun h => hj (Finset.mem_of_mem_erase h)
      have hU : rank (insert j (S.erase k)) < rank S := by
        unfold rank
        rw [Finset.sum_insert hjT]
        have he := Finset.sum_erase_add S (fun j : Fin n => j.val+1) hk
        have hjk' : j.val < k.val := hjk
        omega
      have hh := hgap S j k hjk hj hk
      rcases le_max_iff.mp hh with hh | hh
      · obtain ⟨i,hi,hf⟩ := ih _ (by omega) (S.erase k) rfl
        exact ⟨i,hi,hh.trans hf⟩
      · obtain ⟨i,hi,hf⟩ := ih _ (by omega) (insert j (S.erase k)) rfl
        exact ⟨i,hi,hh.trans hf⟩
    · by_cases hS : S.Nonempty
      · let k := S.max' hS
        have hk : k ∈ S := Finset.max'_mem _ _
        have hkn : k.val+1 ≤ n := by have := k.isLt; omega
        have he : S = popularSet n (k.val+1) := by
          ext j
          simp only [popularSet, Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hj
            have := Finset.le_max' S j hj
            change j.val ≤ k.val at this
            omega
          · intro hj
            by_cases he : j = k
            · simpa [he] using hk
            · by_contra hn
              have hjk : j < k := by have := Fin.ext_iff.not.mp he; change j.val < k.val; omega
              exact hg ⟨j,k,hjk,hn,hk⟩
        exact ⟨k.val+1,hkn,by rw [← he]⟩
      · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
        exact ⟨0,Nat.zero_le _,by simp [he, popularSet]⟩

private lemma prefix_max {n : ℕ} (F : Finset (Fin n) → ℝ)
    (hgap : ∀ S (j k : Fin n), j < k → j ∉ S → k ∈ S →
      F S ≤ max (F (S.erase k)) (F (insert j (S.erase k)))) :
    ∃ i : ℕ, i ≤ n ∧ ∀ S, F S ≤ F (popularSet n i) := by
  classical
  obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_sup' (s := Finset.range (n+1))
    (by simp : (Finset.range (n+1)).Nonempty) (fun i => F (popularSet n i))
  refine ⟨i,by simpa using Finset.mem_range.mp hi,?_⟩
  intro S
  obtain ⟨j,hj,hh⟩ := prefix_dom F hgap S
  apply hh.trans
  rw [← he]
  exact Finset.le_sup' (fun i => F (popularSet n i)) (by simp; omega)

private lemma qc_between (M : ℝ) (hM : 0 < M) (f : ℝ → ℝ)
    (hf : QuasiconvexOn ℝ (Set.Icc 0 M) f) (u w : ℝ)
    (hu : 0 ≤ u) (huw : u ≤ w) (hw : w ≤ M) (hw0 : 0 < w) :
    f u ≤ max (f 0) (f w) := by
  have hb : 0 ≤ u/w := div_nonneg hu hw0.le
  have hb1 : u/w ≤ 1 := (div_le_one hw0).mpr huw
  have hh := (quasiconvexOn_iff_le_max.mp hf).2
    (show 0 ∈ Set.Icc 0 M by constructor; rfl; exact hM.le)
    (show w ∈ Set.Icc 0 M from ⟨hw0.le,hw⟩)
    (sub_nonneg.mpr hb1) hb (by ring : 1-u/w+u/w=1)
  have he : (1-u/w)*0+u/w*w = u := by field_simp; ring
  simpa only [smul_eq_mul, he] using hh

private lemma gap_pos (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ j, 0 < v j) (hv0 : 0 < v0) (hanti : Antitone v)
    (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hβ : 0 < β)
    (S : Finset (Fin n)) (j k : Fin n) (hjk : j < k) (hj : j ∉ S) (hk : k ∈ S) :
    profitI p c lam σ β v v0 S ≤
      max (profitI p c lam σ β v v0 (S.erase k))
        (profitI p c lam σ β v v0 (insert j (S.erase k))) ∧
    profitT p c lam v v0 S ≤
      max (profitT p c lam v v0 (S.erase k))
        (profitT p c lam v v0 (insert j (S.erase k))) := by
  have hq := qc_pair n hn v v0 hv hv0 hanti p c lam σ β hc hcp hlam hσ hβ0 hβ1 (S.erase k)
  have hep := endpoints v v0 hv hv0 p c lam σ β hc hcp hlam hσ hβ0 hβ1 (S.erase k)
  have hkj : v k ≤ v j := hanti hjk.le
  have hjM : v j ≤ v ⟨0,hn⟩ := hanti (by change 0 ≤ j.val; omega)
  have hi := qc_between _ (hv _) _ hq.1 (v k) (v j) (hv k).le hkj hjM (hv j)
  have ht := qc_between _ (hv _) _ hq.2 (v k) (v j) (hv k).le hkj hjM (hv j)
  have hj' : j ∉ S.erase k := fun h => hj (Finset.mem_of_mem_erase h)
  rw [hep.1 k (by simp), Finset.insert_erase hk,
    hep.2.2.2 hβ, hep.1 j hj'] at hi
  rw [hep.2.1 k (by simp), Finset.insert_erase hk,
    hep.2.2.1, hep.2.1 j hj'] at ht
  exact ⟨hi,ht⟩

private lemma gap_zero {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (hanti : Antitone v) (p c lam σ : ℝ)
    (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (S : Finset (Fin n)) (j k : Fin n) (hjk : j < k) (hj : j ∉ S) (hk : k ∈ S) :
    profitI p c lam σ 0 v v0 S ≤ profitI p c lam σ 0 v v0 (insert j (S.erase k)) := by
  classical
  let T := insert j (S.erase k)
  have hj' : j ∉ S.erase k := fun h => hj (Finset.mem_of_mem_erase h)
  have hsum : ∑ i ∈ S, v i ≤ ∑ i ∈ T, v i := by
    dsimp [T]
    rw [Finset.sum_insert hj']
    have he := Finset.sum_erase_add S v hk
    have hh := hanti hjk.le
    linarith
  have hcard : T.card = S.card := by
    dsimp [T]
    simp only [Finset.card_insert_of_notMem hj', Finset.card_erase_of_mem hk]
    have := Finset.card_pos.mpr ⟨k,hk⟩
    omega
  have hshare : (∑ i ∈ S, v i)/(∑ i ∈ S, v i+v0) ≤
      (∑ i ∈ T, v i)/(∑ i ∈ T, v i+v0) := by
    apply (div_le_div_iff₀ (den_pos v v0 hv hv0 S) (den_pos v v0 hv hv0 T)).mpr
    nlinarith
  have hnS : ∀ i ∈ S, share v v0 S i ≠ 0 := by
    intro i hi; exact ne_of_gt (div_pos (hv i) (den_pos v v0 hv hv0 S))
  change profitI p c lam σ 0 v v0 S ≤ profitI p c lam σ 0 v v0 T
  unfold profitI
  simp only [Real.rpow_zero, Finset.sum_const, nsmul_eq_mul, mul_one, hcard]
  simp only [share, ← Finset.sum_div]
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left hshare (by positivity : 0 ≤ (p-c)*lam)) _

theorem solution (n : ℕ) (hn : 0 < n) (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j)
    (hv0 : 0 < v0) (hanti : Antitone v) (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p)
    (hlam : 0 < lam) (hσ : 0 < σ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∃ i : ℕ, i ≤ n ∧ ∀ S : Finset (Fin n),
        profitI p c lam σ β v v0 S ≤ profitI p c lam σ β v v0 (popularSet n i)) ∧
      (∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧ ∀ S : Finset (Fin n),
        profitT p c lam v v0 S ≤ profitT p c lam v v0 (popularSet n i))  := by
  classical
  constructor
  · apply prefix_max
    intro S j k hjk hj hk
    by_cases hb : β = 0
    · subst β
      exact (gap_zero v v0 hv hv0 hanti p c lam σ hc hcp hlam S j k hjk hj hk).trans (le_max_right _ _)
    · exact (gap_pos n hn v v0 hv hv0 hanti p c lam σ β hc hcp hlam hσ hβ0 hβ1
        (lt_of_le_of_ne hβ0 (Ne.symm hb)) S j k hjk hj hk).1
  · obtain ⟨i,hi,hF⟩ := prefix_max (profitT p c lam v v0) (by
      intro S j k hjk hj hk
      exact (gap_pos n hn v v0 hv hv0 hanti p c lam σ (1/2) hc hcp hlam hσ
        (by norm_num) (by norm_num) (by norm_num) S j k hjk hj hk).2)
    by_cases hi0 : i = 0
    · subst i
      refine ⟨1,le_rfl,hn,?_⟩
      intro S
      have hh := hF S
      have hz : profitT p c lam v v0 (popularSet n 0) = 0 := by simp [popularSet, profitT]
      rw [hz] at hh
      exact hh.trans (Finset.sum_nonneg (fun j hj => mul_nonneg (le_max_right _ _) hlam.le))
    · exact ⟨i,by omega,hi,hF⟩
#print axioms solution
