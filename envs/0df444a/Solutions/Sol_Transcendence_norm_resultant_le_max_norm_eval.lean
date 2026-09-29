-- Prove2me | solution 1 for Transcendence.norm_resultant_le_max_norm_eval
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-27T08:16:50.194977+00:00
-- url     : https://prove2.me/submissions/526d9b69-0940-4180-a9d3-ed79ec81f515

import Mathlib

/-!
# A Liouville inequality through the resultant

Let `F, G ∈ ℂ[X]` have Mahler measures at least `1`. Then at every point `θ`,
`|Res(F, G)| ≤ 2^(deg F · deg G) · M(F)^(deg G) · M(G)^(deg F) · max(|F(θ)|, |G(θ)|)`.

Let `α₁` be the root of `F` or `G` nearest to `θ`, say a root of `F`. Writing the resultant as
`a^(deg G) ∏ G(α)` over the roots `α` of `F`, the factor `G(α₁)` is at most `2^(deg G) |G(θ)|`,
because every root `β` of `G` has `|α₁ - β| ≤ 2 |θ - β|`, and each other factor `G(α)` is at most
`2^(deg G) max(1, |α|)^(deg G) M(G)`. If neither polynomial has a root, both are constants and the
resultant is `1 ≤ M(F) = |F(θ)|`. This is the complex form of the inequality of Roy–Waldschmidt
(1997), Corollary 3.7, proved as in their Lemma 3.4: when `F, G ∈ ℤ[X]` are coprime, the resultant
is a non-zero integer and the right-hand side is at least `1`.
-/

namespace S7W4_norm_resultant_le_max_norm_eval

open Polynomial

lemma norm_prod_map {ι : Type*} (s : Multiset ι) (f : ι → ℂ) :
    ‖(s.map f).prod‖ = (s.map fun i => ‖f i‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

/-- At a root `α₁` nearer to `θ` than every root of `G`: `|G(α₁)| ≤ 2ⁿ |G(θ)|`. -/
lemma eval_near (G : ℂ[X]) (θ α1 : ℂ) (hnear : ∀ β ∈ G.roots, ‖θ - α1‖ ≤ ‖θ - β‖) :
    ‖G.eval α1‖ ≤ 2 ^ G.natDegree * ‖G.eval θ‖ := by
  rw [(IsAlgClosed.splits G).eval_eq_prod_roots α1, (IsAlgClosed.splits G).eval_eq_prod_roots θ,
    norm_mul, norm_mul, norm_prod_map, norm_prod_map]
  have hle := Multiset.prod_map_le_prod_map₀ (s := G.roots) (fun β => ‖α1 - β‖)
    (fun β => 2 * ‖θ - β‖) (fun _ _ => norm_nonneg _) (fun β hβ => by
      have h1 := norm_sub_le_norm_sub_add_norm_sub α1 θ β
      rw [norm_sub_rev α1 θ] at h1
      linarith [hnear β hβ])
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    IsAlgClosed.card_roots_eq_natDegree] at hle
  calc ‖G.leadingCoeff‖ * (G.roots.map fun β => ‖α1 - β‖).prod
      ≤ ‖G.leadingCoeff‖ * (2 ^ G.natDegree * (G.roots.map fun β => ‖θ - β‖).prod) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = _ := by ring

/-- Anywhere: `|G(a)| ≤ 2ⁿ max(1,|a|)ⁿ M(G)`. -/
lemma eval_far (G : ℂ[X]) (a : ℂ) :
    ‖G.eval a‖ ≤ 2 ^ G.natDegree * max 1 ‖a‖ ^ G.natDegree * G.mahlerMeasure := by
  rw [(IsAlgClosed.splits G).eval_eq_prod_roots a, mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    norm_mul, norm_prod_map]
  have hle := Multiset.prod_map_le_prod_map₀ (s := G.roots) (fun β => ‖a - β‖)
    (fun β => (2 * max 1 ‖a‖) * max 1 ‖β‖) (fun _ _ => norm_nonneg _) (fun β _ => by
      have h1 := norm_sub_le a β
      have h2 : ‖a‖ ≤ max 1 ‖a‖ := le_max_right _ _
      have h3 : ‖β‖ ≤ max 1 ‖β‖ := le_max_right _ _
      have h4 : (1 : ℝ) ≤ max 1 ‖a‖ := le_max_left _ _
      have h5 : (1 : ℝ) ≤ max 1 ‖β‖ := le_max_left _ _
      nlinarith [mul_le_mul h2 h5 zero_le_one (by linarith),
        mul_le_mul h4 h3 (norm_nonneg _) (by linarith)])
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    IsAlgClosed.card_roots_eq_natDegree] at hle
  calc ‖G.leadingCoeff‖ * (G.roots.map fun β => ‖a - β‖).prod
      ≤ ‖G.leadingCoeff‖ * ((2 * max 1 ‖a‖) ^ G.natDegree *
          (G.roots.map fun β => max 1 ‖β‖).prod) :=
        mul_le_mul_of_nonneg_left hle (norm_nonneg _)
    _ = _ := by rw [mul_pow]; ring

/-- The root product in `Res(F, G) = a^n ∏ G(α)`, when a root `α₁` of `F` is nearest to `θ`. -/
lemma bound_near (F G : ℂ[X]) (θ α1 : ℂ) (h1 : α1 ∈ F.roots)
    (hnear : ∀ β ∈ G.roots, ‖θ - α1‖ ≤ ‖θ - β‖) (hG1 : 1 ≤ G.mahlerMeasure) :
    ‖F.leadingCoeff ^ G.natDegree * (F.roots.map G.eval).prod‖
      ≤ 2 ^ (F.natDegree * G.natDegree) * F.mahlerMeasure ^ G.natDegree
        * G.mahlerMeasure ^ F.natDegree * ‖G.eval θ‖ := by
  obtain ⟨s, hs⟩ : ∃ s, F.roots = α1 ::ₘ s := ⟨_, (Multiset.cons_erase h1).symm⟩
  have hcard : Multiset.card s + 1 = F.natDegree := by
    have := IsAlgClosed.card_roots_eq_natDegree (p := F)
    rw [hs, Multiset.card_cons] at this
    exact this
  have hmax0 : 0 ≤ (s.map fun a => max 1 ‖a‖).prod := Multiset.prod_nonneg fun x hx => by
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
    exact zero_le_one.trans (le_max_left _ _)
  have hMF : ‖F.leadingCoeff‖ * (s.map fun a => max 1 ‖a‖).prod ≤ F.mahlerMeasure := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots F, hs, Multiset.map_cons, Multiset.prod_cons]
    have hnn : 0 ≤ ‖F.leadingCoeff‖ * (s.map fun a => max 1 ‖a‖).prod :=
      mul_nonneg (norm_nonneg _) hmax0
    nlinarith [le_max_left 1 ‖α1‖]
  have hP0 : 0 ≤ (s.map fun a => ‖G.eval a‖).prod := Multiset.prod_nonneg fun x hx => by
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
    exact norm_nonneg _
  have hA := eval_near G θ α1 (fun β hβ => hnear β hβ)
  have hB := Multiset.prod_map_le_prod_map₀ (s := s) (fun a => ‖G.eval a‖)
    (fun a => 2 ^ G.natDegree * max 1 ‖a‖ ^ G.natDegree * G.mahlerMeasure)
    (fun _ _ => norm_nonneg _) (fun a _ => eval_far G a)
  have hfun : (fun a : ℂ => 2 ^ G.natDegree * max 1 ‖a‖ ^ G.natDegree * G.mahlerMeasure)
      = fun a => (2 ^ G.natDegree * G.mahlerMeasure) * max 1 ‖a‖ ^ G.natDegree := by
    funext a; ring
  rw [hfun, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate,
    Multiset.prod_map_pow] at hB
  rw [norm_mul, norm_pow, hs, Multiset.map_cons, Multiset.prod_cons, norm_mul, norm_prod_map]
  have hMG0 : 0 ≤ G.mahlerMeasure := zero_le_one.trans hG1
  have hMF0 : 0 ≤ F.mahlerMeasure := (mul_nonneg (norm_nonneg _) hmax0).trans hMF
  calc ‖F.leadingCoeff‖ ^ G.natDegree * (‖G.eval α1‖ * (s.map fun a => ‖G.eval a‖).prod)
      ≤ ‖F.leadingCoeff‖ ^ G.natDegree * ((2 ^ G.natDegree * ‖G.eval θ‖)
          * ((2 ^ G.natDegree * G.mahlerMeasure) ^ Multiset.card s
            * (s.map fun a => max 1 ‖a‖).prod ^ G.natDegree)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hA hB hP0 (by positivity)) (by positivity)
    _ = 2 ^ G.natDegree * (2 ^ G.natDegree) ^ Multiset.card s
          * (‖F.leadingCoeff‖ * (s.map fun a => max 1 ‖a‖).prod) ^ G.natDegree
          * G.mahlerMeasure ^ Multiset.card s * ‖G.eval θ‖ := by ring
    _ ≤ 2 ^ G.natDegree * (2 ^ G.natDegree) ^ Multiset.card s * F.mahlerMeasure ^ G.natDegree
          * G.mahlerMeasure ^ (Multiset.card s + 1) * ‖G.eval θ‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul _ (pow_le_pow_right₀ hG1 (Nat.le_succ _)) (pow_nonneg hMG0 _)
          (mul_nonneg (by positivity) (pow_nonneg hMF0 _))
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hmax0) hMF _) (by positivity)
    _ = _ := by
        rw [← hcard, show (Multiset.card s + 1) * G.natDegree = G.natDegree * (Multiset.card s + 1)
          by ring, pow_mul, pow_succ]
        ring

end S7W4_norm_resultant_le_max_norm_eval

open Polynomial S7W4_norm_resultant_le_max_norm_eval in
theorem solution (F G : Polynomial ℂ) (hF : 1 ≤ F.mahlerMeasure)
    (hG : 1 ≤ G.mahlerMeasure) (θ : ℂ) :
    ‖F.resultant G‖ ≤ 2 ^ (F.natDegree * G.natDegree) * F.mahlerMeasure ^ G.natDegree *
      G.mahlerMeasure ^ F.natDegree * max ‖F.eval θ‖ ‖G.eval θ‖ := by
  classical
  rcases ((F.roots + G.roots).toFinset).eq_empty_or_nonempty with hemp | hne
  · -- two constants: the resultant is `1 ≤ M(F) = |F(θ)|`
    rw [Multiset.toFinset_eq_empty, add_eq_zero] at hemp
    have hF0 : F.natDegree = 0 := by
      rw [← IsAlgClosed.card_roots_eq_natDegree, hemp.1, Multiset.card_zero]
    have hG0 : G.natDegree = 0 := by
      rw [← IsAlgClosed.card_roots_eq_natDegree, hemp.2, Multiset.card_zero]
    rw [eq_C_of_natDegree_eq_zero hF0, mahlerMeasure_const] at hF
    rw [hF0, hG0, resultant_zero_left_deg, eq_C_of_natDegree_eq_zero hF0, eval_C]
    simpa using le_max_of_le_left hF
  obtain ⟨z, hzS, hzmin⟩ := Finset.exists_min_image _ (fun x => ‖θ - x‖) hne
  have hmem : ∀ x, x ∈ F.roots ∨ x ∈ G.roots → ‖θ - z‖ ≤ ‖θ - x‖ := fun x hx =>
    hzmin x (Multiset.mem_toFinset.2 (Multiset.mem_add.2 hx))
  rcases Multiset.mem_add.1 (Multiset.mem_toFinset.1 hzS) with hz | hz
  · have e := resultant_eq_prod_eval F G G.natDegree le_rfl (IsAlgClosed.splits F)
    have hb := bound_near F G θ z hz (fun β hβ => hmem β (Or.inr hβ)) hG
    rw [← e] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity))
  · have e := resultant_eq_prod_eval G F F.natDegree le_rfl (IsAlgClosed.splits G)
    have hb := bound_near G F θ z hz (fun β hβ => hmem β (Or.inl hβ)) hF
    rw [← e] at hb
    have hcomm : ‖F.resultant G‖ = ‖G.resultant F‖ := by rw [resultant_comm]; simp
    rw [hcomm]
    refine hb.trans ?_
    calc _ = 2 ^ (F.natDegree * G.natDegree) * F.mahlerMeasure ^ G.natDegree
          * G.mahlerMeasure ^ F.natDegree * ‖F.eval θ‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

#print axioms solution
