-- Prove2me | solution 1 for TheoryOfGames.CharFun.charFun_isCharFunction
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:18:43.580457+00:00
-- url     : https://prove2.me/submissions/fce92fdf-70c9-44bf-9b03-c7080d5e1493

import Definitions.Def_TheoryOfGames_CharFun_charFun
import Definitions.Def_TheoryOfGames_CharFun_IsCharFunction

/-!
# 25.3.1: properties of the characteristic function

For a zero-sum `n`-person game with characteristic function
`v(S) = ⨆_ξ ⨅_η K(ξ, η)` (`ξ` over the mixed strategies of the composite player `S`, `η`
over those of `-S`, `K` the bilinear form of the two-person game):

* **(25:3:a)** `v(∅) = 0` — the empty coalition's payoff is `0` identically.
* **(25:3:b)** `v(-S) = -v(S)` — the composite game of `-S` against `S` is the negation of
  that of `S` against `-S` (the two full profiles assembled from the same aggregates
  coincide, and the total payoff is `0`), so `K_{-S}(η, ξ) = -K_S(ξ, η)`; then
  **Sion's minimax theorem** (`Mathlib.Topology.Sion.minimax'`, applicable since the
  simplices are compact convex and `K` is bilinear) exchanges `⨆` and `⨅`, giving the sign
  change on the level of `v`.
* **(25:3:c)** superadditivity on disjoint sets — the composite player of `S ∪ T` can play
  the *product* of almost-optimal mixed strategies of `S` and of `T`; against any `η`, the
  payoff splits into the `S`-part against the marginal (a valid opponent for `S`) plus the
  `T`-part against a valid opponent for `T`, hence is at least `v(S) - ε + v(T) - ε`.
-/

open TheoryOfGames.CharFun

namespace CFAux

open ZeroSumGame

variable {n : ℕ} (Γ : ZeroSumGame n)

/-- Every coalition has aggregates (all `β k ≥ 1`). -/
private lemma nonempty_coalStrat (S : Finset (Fin n)) :
    Nonempty (Γ.CoalStrat S) :=
  ⟨fun k => Fin.mk 0 (Γ.β_pos k.1)⟩

/-- The probability simplex on a nonempty type is nonempty. -/
private lemma nonempty_simplex {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] :
    Nonempty (stdSimplex ℝ X) :=
  ⟨Pi.single (Classical.arbitrary X) 1,
    single_mem_stdSimplex (𝕜 := ℝ) (Classical.arbitrary X)⟩

/-- Elements of the simplex sum to one. -/
private lemma simplex_sum {X : Type} [Fintype X] [DecidableEq X] (ξ : stdSimplex ℝ X) :
    ∑ i, (ξ : X → ℝ) i = 1 :=
  stdSimplex.sum_eq_one ξ

section Symmetry

/-- The canonical identification of `Sᶜᶜ` with `S`, as an explicit equivalence. -/
private def castE (S : Finset (Fin n)) :
    Γ.CoalStrat S ≃ Γ.CoalStrat Sᶜᶜ where
  toFun τS k := τS ⟨(k : Fin n), by simpa using k.2⟩
  invFun τS' k := τS' ⟨(k : Fin n), by simpa using k.2⟩
  left_inv := by
    intro τS
    funext k
    rfl
  right_inv := by
    intro τS'
    funext k
    rfl

/-- The full profile assembled from `τS` and `τC` equals the one assembled the other way. -/
private lemma joint_swap (S : Finset (Fin n)) (τS : Γ.CoalStrat S) (τC : Γ.CoalStrat Sᶜ) :
    Γ.joint Sᶜ τC (castE Γ S τS) = Γ.joint S τS τC := by
  funext k
  by_cases hk : k ∈ S <;>
    simp [ZeroSumGame.joint, hk, castE, Equiv.cast]

/-- The payoff of `-S` against `S` is the negative of the payoff of `S` against `-S`. -/
private lemma coalPayoff_neg (S : Finset (Fin n)) (τS : Γ.CoalStrat S)
    (τC : Γ.CoalStrat Sᶜ) :
    Γ.coalPayoff Sᶜ τC (castE Γ S τS) = -Γ.coalPayoff S τS τC := by
  have hjoint : Γ.joint Sᶜ τC (castE Γ S τS) = Γ.joint S τS τC := joint_swap Γ S τS τC
  have h1 : ∑ k ∈ S, Γ.H (Γ.joint S τS τC) k + ∑ k ∈ Sᶜ, Γ.H (Γ.joint S τS τC) k = 0 := by
    rw [Finset.sum_add_sum_compl, Γ.zero_sum (Γ.joint S τS τC)]
  simp only [ZeroSumGame.coalPayoff, hjoint]
  linarith

/-- The bilinear form of `-S` is the negated transpose of that of `S`. -/
private lemma bilin_neg_swap (S : Finset (Fin n))
    (a : Γ.CoalStrat S → ℝ) (b : Γ.CoalStrat Sᶜ → ℝ) :
    Γ.bilin Sᶜ b (fun x => a ((castE Γ S).symm x)) = -Γ.bilin S a b := by
  set e := castE Γ S with he
  have hterm : ∀ (τC : Γ.CoalStrat Sᶜ) (τS : Γ.CoalStrat S),
      Γ.coalPayoff Sᶜ τC (e τS) * b τC * a τS
        = -(Γ.coalPayoff S τS τC * a τS * b τC) := by
    intro τC τS
    rw [coalPayoff_neg Γ S τS τC]
    ring
  -- reindex the inner sum over the equivalence
  have hreidx : ∀ τC : Γ.CoalStrat Sᶜ,
      (∑ τS' : Γ.CoalStrat Sᶜᶜ,
          Γ.coalPayoff Sᶜ τC τS' * b τC * a (e.symm τS'))
        = ∑ τS : Γ.CoalStrat S,
          Γ.coalPayoff Sᶜ τC (e τS) * b τC * a τS := by
    intro τC
    exact Fintype.sum_equiv e.symm
      (fun τS' => Γ.coalPayoff Sᶜ τC τS' * b τC * a (e.symm τS'))
      (fun τS => Γ.coalPayoff Sᶜ τC (e τS) * b τC * a τS)
      (fun τS' => by simp [Equiv.symm_apply_apply])
  calc Γ.bilin Sᶜ b (fun x => a ((castE Γ S).symm x))
      = ∑ τC : Γ.CoalStrat Sᶜ, ∑ τS : Γ.CoalStrat S,
          Γ.coalPayoff Sᶜ τC (e τS) * b τC * a τS := by
        rw [show Γ.bilin Sᶜ b (fun x => a ((castE Γ S).symm x))
            = ∑ τC : Γ.CoalStrat Sᶜ, ∑ τS' : Γ.CoalStrat Sᶜᶜ,
                Γ.coalPayoff Sᶜ τC τS' * b τC * a ((castE Γ S).symm τS') from rfl,
          Finset.sum_congr rfl (fun τC _ => hreidx τC)]
    _ = ∑ τC : Γ.CoalStrat Sᶜ, ∑ τS : Γ.CoalStrat S,
          -(Γ.coalPayoff S τS τC * a τS * b τC) :=
        Finset.sum_congr rfl (fun τC _ => Finset.sum_congr rfl (fun τS _ => hterm τC τS))
    _ = -(∑ τC : Γ.CoalStrat Sᶜ, ∑ τS : Γ.CoalStrat S,
          Γ.coalPayoff S τS τC * a τS * b τC) := by
        rw [Finset.sum_congr rfl (fun τC _ =>
          Finset.sum_neg_distrib (f := fun τS => Γ.coalPayoff S τS τC * a τS * b τC))]
        rw [Finset.sum_neg_distrib]
    _ = -(∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ,
          Γ.coalPayoff S τS τC * a τS * b τC) := by
        rw [Finset.sum_comm]
    _ = -Γ.bilin S a b := by
        rfl

section Affinity

/-- The bilinear form is affine in the first argument. -/
private lemma bilin_smul_add (S : Finset (Fin n)) (p q : ℝ)
    (a₁ a₂ : Γ.CoalStrat S → ℝ) (b : Γ.CoalStrat Sᶜ → ℝ) :
    Γ.bilin S (p • a₁ + q • a₂) b = p * Γ.bilin S a₁ b + q * Γ.bilin S a₂ b := by
  show ∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ,
      Γ.coalPayoff S τS τC * (p • a₁ + q • a₂) τS * b τC
    = p * (∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ,
          Γ.coalPayoff S τS τC * a₁ τS * b τC)
      + q * (∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ,
          Γ.coalPayoff S τS τC * a₂ τS * b τC)
  have h1 : ∀ τS : Γ.CoalStrat S, ∀ τC : Γ.CoalStrat Sᶜ,
      Γ.coalPayoff S τS τC * (p • a₁ + q • a₂) τS * b τC
        = p * (Γ.coalPayoff S τS τC * a₁ τS * b τC)
          + q * (Γ.coalPayoff S τS τC * a₂ τS * b τC) := by
    intro τS τC
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun τS _ => Finset.sum_congr rfl (fun τC _ => h1 τS τC))]
  rw [Finset.sum_congr rfl (fun τS _ => Finset.sum_add_distrib)]
  rw [Finset.sum_congr rfl (fun τS _ => by rw [← Finset.mul_sum, ← Finset.mul_sum])]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

/-- The bilinear form is affine in the second argument. -/
private lemma bilin_add_smul (S : Finset (Fin n)) (p q : ℝ)
    (a : Γ.CoalStrat S → ℝ) (b₁ b₂ : Γ.CoalStrat Sᶜ → ℝ) :
    Γ.bilin S a (p • b₁ + q • b₂) = p * Γ.bilin S a b₁ + q * Γ.bilin S a b₂ := by
  show ∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ,
      Γ.coalPayoff S τS τC * a τS * (p • b₁ + q • b₂) τC
    = p * (∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ,
          Γ.coalPayoff S τS τC * a τS * b₁ τC)
      + q * (∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ,
          Γ.coalPayoff S τS τC * a τS * b₂ τC)
  have h1 : ∀ τS : Γ.CoalStrat S, ∀ τC : Γ.CoalStrat Sᶜ,
      Γ.coalPayoff S τS τC * a τS * (p • b₁ + q • b₂) τC
        = p * (Γ.coalPayoff S τS τC * a τS * b₁ τC)
          + q * (Γ.coalPayoff S τS τC * a τS * b₂ τC) := by
    intro τS τC
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun τS _ => Finset.sum_congr rfl (fun τC _ => h1 τS τC))]
  rw [Finset.sum_congr rfl (fun τS _ => Finset.sum_add_distrib)]
  rw [Finset.sum_congr rfl (fun τS _ => by rw [← Finset.mul_sum, ← Finset.mul_sum])]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]

end Affinity

end Symmetry

section NegPush

/-- Pushing a negation through an infimum (ℝ, nonempty index). -/
private lemma iInf_neg_eq' {X : Type} [Nonempty X] (g : X → ℝ) : (⨅ i, -g i) = -⨆ i, g i := by
  have h : (Set.range fun i => -g i) = -Set.range (fun i => g i) := by
    ext y
    simp only [Set.mem_range, Set.mem_neg]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, by ring⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, by linarith⟩
  simp only [iInf, iSup, h, Real.sInf_neg]

/-- Pushing a negation through a supremum (ℝ, nonempty index). -/
private lemma iSup_neg_eq' {X : Type} [Nonempty X] (g : X → ℝ) : (⨆ i, -g i) = -⨅ i, g i := by
  have h3 : (⨅ i, g i) = -(⨆ i, -g i) := by
    simpa using iInf_neg_eq' (fun i => -g i)
  linarith

/-- Supremum is invariant under reindexing by an equivalence. -/
private lemma iSup_bij {X Y : Type} (e : X ≃ Y) (F : Y → ℝ) : (⨆ y, F y) = (⨆ x, F (e x)) := by
  rw [iSup, iSup]
  congr 1
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e.symm y, by simp⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e x, rfl⟩

end NegPush

section PartA

/-- (25:3:a): the empty coalition's value is `0`. -/
private lemma charFun_empty : Γ.charFun ∅ = 0 := by
  haveI hx : Nonempty (Γ.CoalStrat ∅) := nonempty_coalStrat Γ ∅
  haveI hy : Nonempty (Γ.CoalStrat (∅ : Finset (Fin n))ᶜ) := nonempty_coalStrat Γ _
  haveI hX : Nonempty (stdSimplex ℝ (Γ.CoalStrat ∅)) := nonempty_simplex
  haveI hY : Nonempty (stdSimplex ℝ (Γ.CoalStrat (∅ : Finset (Fin n))ᶜ)) := nonempty_simplex
  have hbilin : ∀ (ξ : stdSimplex ℝ (Γ.CoalStrat ∅))
      (η : stdSimplex ℝ (Γ.CoalStrat (∅ : Finset (Fin n))ᶜ)),
      Γ.bilin ∅ (↑ξ) (↑η) = 0 := by
    intro ξ η
    show ∑ τS : Γ.CoalStrat ∅, ∑ τC : Γ.CoalStrat (∅ : Finset (Fin n))ᶜ,
        Γ.coalPayoff ∅ τS τC * (↑ξ : _ → ℝ) τS * (↑η : _ → ℝ) τC = 0
    simp [ZeroSumGame.coalPayoff]
  calc Γ.charFun ∅
      = ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat ∅),
          ⨅ η : stdSimplex ℝ (Γ.CoalStrat (∅ : Finset (Fin n))ᶜ),
            Γ.bilin ∅ (↑ξ) (↑η) := rfl
    _ = (0 : ℝ) := by
        have hpoint : ∀ ξ : stdSimplex ℝ (Γ.CoalStrat ∅),
            (⨅ η : stdSimplex ℝ (Γ.CoalStrat (∅ : Finset (Fin n))ᶜ), Γ.bilin ∅ (↑ξ) (↑η))
              = (0 : ℝ) := by
          intro ξ
          calc (⨅ η : stdSimplex ℝ (Γ.CoalStrat (∅ : Finset (Fin n))ᶜ), Γ.bilin ∅ (↑ξ) (↑η))
              = ⨅ η : stdSimplex ℝ (Γ.CoalStrat (∅ : Finset (Fin n))ᶜ), (0 : ℝ) :=
                congrArg iInf (funext (fun η => hbilin ξ η))
            _ = 0 := by simp
        calc Γ.charFun ∅
            = ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat ∅),
                ⨅ η : stdSimplex ℝ (Γ.CoalStrat (∅ : Finset (Fin n))ᶜ),
                  Γ.bilin ∅ (↑ξ) (↑η) := rfl
          _ = ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat ∅), (0 : ℝ) :=
                congrArg iSup (funext hpoint)
          _ = 0 := by simp
    _ = 0 := by simp

end PartA

set_option maxHeartbeats 800000
section Sion

/-- The bilinear form is continuous in the first argument. -/
private lemma continuous_bilin_left (S : Finset (Fin n)) (y : Γ.CoalStrat Sᶜ → ℝ) :
    Continuous (fun x : Γ.CoalStrat S → ℝ => Γ.bilin S x y) := by
  unfold ZeroSumGame.bilin
  exact continuous_finset_sum _ fun τS _ =>
    continuous_finset_sum _ fun τC _ => by fun_prop

/-- The bilinear form is continuous in the second argument. -/
private lemma continuous_bilin_right (S : Finset (Fin n)) (x : Γ.CoalStrat S → ℝ) :
    Continuous (fun y : Γ.CoalStrat Sᶜ → ℝ => Γ.bilin S x y) := by
  unfold ZeroSumGame.bilin
  exact continuous_finset_sum _ fun τS _ =>
    continuous_finset_sum _ fun τC _ => by fun_prop

/-- The bilinear form is quasiconvex in the first argument (affinity). -/
private lemma quasiconvexOn_bilin (S : Finset (Fin n)) (y : Γ.CoalStrat Sᶜ → ℝ) :
    QuasiconvexOn ℝ (stdSimplex ℝ (Γ.CoalStrat S))
      (fun x : Γ.CoalStrat S → ℝ => Γ.bilin S x y) := by
  intro r
  rw [convex_iff_add_mem]
  intro x₁ hx₁ x₂ hx₂ a ha h1 h2 h3
  dsimp only at hx₁ hx₂
  refine ⟨(convex_iff_add_mem.mp (convex_stdSimplex ℝ (Γ.CoalStrat S))) hx₁.1 hx₂.1 h1 h2 h3, ?_⟩
  show Γ.bilin S (a • x₁ + ha • x₂) y ≤ r
  rw [bilin_smul_add]
  have e1 : a * Γ.bilin S x₁ y ≤ a * r := mul_le_mul_of_nonneg_left hx₁.2 h1
  have e2 : ha * Γ.bilin S x₂ y ≤ ha * r := mul_le_mul_of_nonneg_left hx₂.2 h2
  have e4 : a * r + ha * r = r := by
    linear_combination h3 * r
  linarith

/-- The bilinear form is quasiconcave in the second argument (affinity). -/
private lemma quasiconcaveOn_bilin (S : Finset (Fin n)) (x : Γ.CoalStrat S → ℝ) :
    QuasiconcaveOn ℝ (stdSimplex ℝ (Γ.CoalStrat Sᶜ))
      (fun y : Γ.CoalStrat Sᶜ → ℝ => Γ.bilin S x y) := by
  intro r
  rw [convex_iff_add_mem]
  intro y₁ hy₁ y₂ hy₂ a ha h1 h2 h3
  dsimp only at hy₁ hy₂
  refine ⟨(convex_iff_add_mem.mp (convex_stdSimplex ℝ (Γ.CoalStrat Sᶜ))) hy₁.1 hy₂.1 h1 h2 h3, ?_⟩
  show Γ.bilin S x (a • y₁ + ha • y₂) ≥ r
  rw [bilin_add_smul]
  have e1 : r * a ≤ Γ.bilin S x y₁ * a := mul_le_mul_of_nonneg_right hy₁.2 h1
  have e2 : r * ha ≤ Γ.bilin S x y₂ * ha := mul_le_mul_of_nonneg_right hy₂.2 h2
  have e4 : r * a + r * ha = r := by
    linear_combination h3 * r
  linarith

/-- Rewriting the bilinear form as a convex combination in the second argument. -/
private lemma bilin_swap (S : Finset (Fin n)) (x : Γ.CoalStrat S → ℝ) (y : Γ.CoalStrat Sᶜ → ℝ) :
    Γ.bilin S x y
      = ∑ τC : Γ.CoalStrat Sᶜ, y τC * (∑ τS : Γ.CoalStrat S, Γ.coalPayoff S τS τC * x τS) := by
  have hterm : ∀ (τS : Γ.CoalStrat S) (τC : Γ.CoalStrat Sᶜ),
      Γ.coalPayoff S τS τC * x τS * y τC
        = y τC * (Γ.coalPayoff S τS τC * x τS) := by
    intro τS τC
    ring
  unfold ZeroSumGame.bilin
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun τC _ => Finset.sum_congr rfl (fun τS _ => hterm τS τC))]
  exact Finset.sum_congr rfl (fun τC _ =>
    (Finset.mul_sum (s := Finset.univ)
      (f := fun τS => Γ.coalPayoff S τS τC * x τS) (a := y τC)).symm)

/-- The bilinear form is uniformly bounded on the two simplices. -/
private lemma abs_bilin_le (S : Finset (Fin n)) {x : Γ.CoalStrat S → ℝ}
    {y : Γ.CoalStrat Sᶜ → ℝ} (hx : x ∈ stdSimplex ℝ (Γ.CoalStrat S))
    (hy : y ∈ stdSimplex ℝ (Γ.CoalStrat Sᶜ)) :
    |Γ.bilin S x y| ≤ ∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ,
      |Γ.coalPayoff S τS τC| := by
  have hx01 : ∀ τS, x τS ∈ Set.Icc (0 : ℝ) 1 := fun τS => mem_Icc_of_mem_stdSimplex hx τS
  have hy01 : ∀ τC, y τC ∈ Set.Icc (0 : ℝ) 1 := fun τC => mem_Icc_of_mem_stdSimplex hy τC
  have hterm : ∀ (τS : Γ.CoalStrat S) (τC : Γ.CoalStrat Sᶜ),
      |Γ.coalPayoff S τS τC * x τS * y τC| ≤ |Γ.coalPayoff S τS τC| := by
    intro τS τC
    have h1 : |x τS| ≤ 1 := by
      rw [abs_of_nonneg (hx01 τS).1]
      exact (hx01 τS).2
    have h2 : |y τC| ≤ 1 := by
      rw [abs_of_nonneg (hy01 τC).1]
      exact (hy01 τC).2
    have hxy : |x τS| * |y τC| ≤ 1 := by
      nlinarith [h1, h2, abs_nonneg (x τS), abs_nonneg (y τC)]
    rw [abs_mul, abs_mul]
    nlinarith [hxy, abs_nonneg (Γ.coalPayoff S τS τC), abs_nonneg (x τS), abs_nonneg (y τC)]
  show |∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ,
      Γ.coalPayoff S τS τC * x τS * y τC|
    ≤ ∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ, |Γ.coalPayoff S τS τC|
  have h1 : |∑ τS : Γ.CoalStrat S,
      ∑ τC : Γ.CoalStrat Sᶜ, Γ.coalPayoff S τS τC * x τS * y τC|
      ≤ ∑ τS : Γ.CoalStrat S,
          |∑ τC : Γ.CoalStrat Sᶜ, Γ.coalPayoff S τS τC * x τS * y τC| :=
    Finset.abs_sum_le_sum_abs _ _
  have h2 : ∀ τS : Γ.CoalStrat S,
      |∑ τC : Γ.CoalStrat Sᶜ, Γ.coalPayoff S τS τC * x τS * y τC|
        ≤ ∑ τC : Γ.CoalStrat Sᶜ, |Γ.coalPayoff S τS τC * x τS * y τC| :=
    fun τS => Finset.abs_sum_le_sum_abs _ _
  have h3 : ∑ τS : Γ.CoalStrat S,
      |∑ τC : Γ.CoalStrat Sᶜ, Γ.coalPayoff S τS τC * x τS * y τC|
      ≤ ∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ, |Γ.coalPayoff S τS τC| :=
    Finset.sum_le_sum fun τS _ => le_trans (h2 τS)
      (Finset.sum_le_sum fun τC _ => hterm τS τC)
  exact le_trans (le_trans h1 h3) le_rfl

/-- The bilinear form is quasiconvex in the second argument (affinity). -/
private lemma quasiconvexOn2_bilin (S : Finset (Fin n)) (y : Γ.CoalStrat S → ℝ) :
    QuasiconvexOn ℝ (stdSimplex ℝ (Γ.CoalStrat Sᶜ))
      (fun x : Γ.CoalStrat Sᶜ → ℝ => Γ.bilin S y x) := by
  intro r
  rw [convex_iff_add_mem]
  intro x₁ hx₁ x₂ hx₂ a ha h1 h2 h3
  dsimp only at hx₁ hx₂
  refine ⟨(convex_iff_add_mem.mp (convex_stdSimplex ℝ (Γ.CoalStrat Sᶜ))) hx₁.1 hx₂.1 h1 h2 h3, ?_⟩
  show Γ.bilin S y (a • x₁ + ha • x₂) ≤ r
  rw [bilin_add_smul]
  have e1 : a * Γ.bilin S y x₁ ≤ a * r := mul_le_mul_of_nonneg_left hx₁.2 h1
  have e2 : ha * Γ.bilin S y x₂ ≤ ha * r := mul_le_mul_of_nonneg_left hx₂.2 h2
  have e4 : a * r + ha * r = r := by
    linear_combination h3 * r
  linarith

/-- The bilinear form is quasiconcave in the first argument (affinity). -/
private lemma quasiconcave2_bilin (S : Finset (Fin n)) (x : Γ.CoalStrat Sᶜ → ℝ) :
    QuasiconcaveOn ℝ (stdSimplex ℝ (Γ.CoalStrat S))
      (fun y : Γ.CoalStrat S → ℝ => Γ.bilin S y x) := by
  intro r
  rw [convex_iff_add_mem]
  intro y₁ hy₁ y₂ hy₂ a ha h1 h2 h3
  dsimp only at hy₁ hy₂
  refine ⟨(convex_iff_add_mem.mp (convex_stdSimplex ℝ (Γ.CoalStrat S))) hy₁.1 hy₂.1 h1 h2 h3, ?_⟩
  show Γ.bilin S (a • y₁ + ha • y₂) x ≥ r
  rw [bilin_smul_add]
  have e1 : r * a ≤ Γ.bilin S y₁ x * a := mul_le_mul_of_nonneg_right hy₁.2 h1
  have e2 : r * ha ≤ Γ.bilin S y₂ x * ha := mul_le_mul_of_nonneg_right hy₂.2 h2
  have e4 : r * a + r * ha = r := by
    linear_combination h3 * r
  linarith

/-- Sion's minimax theorem for the bilinear form: sup-inf = inf-sup. -/
private lemma sion_bilin (S : Finset (Fin n)) :
    (⨆ ξ : stdSimplex ℝ (Γ.CoalStrat S),
        ⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ), Γ.bilin S (↑ξ) (↑η))
      = ⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ),
          ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat S), Γ.bilin S (↑ξ) (↑η) := by
  haveI hNS : Nonempty (Γ.CoalStrat S) := nonempty_coalStrat Γ S
  haveI hNT : Nonempty (Γ.CoalStrat Sᶜ) := nonempty_coalStrat Γ _
  haveI hNX : Nonempty (stdSimplex ℝ (Γ.CoalStrat S)) := nonempty_simplex
  haveI hNY : Nonempty (stdSimplex ℝ (Γ.CoalStrat Sᶜ)) := nonempty_simplex
  have hXne : (stdSimplex ℝ (Γ.CoalStrat Sᶜ)).Nonempty :=
    ⟨Pi.single (Classical.arbitrary (Γ.CoalStrat Sᶜ)) 1,
      single_mem_stdSimplex (𝕜 := ℝ) (Classical.arbitrary (Γ.CoalStrat Sᶜ))⟩
  have hYne : (stdSimplex ℝ (Γ.CoalStrat S)).Nonempty :=
    ⟨Pi.single (Classical.arbitrary (Γ.CoalStrat S)) 1,
      single_mem_stdSimplex (𝕜 := ℝ) (Classical.arbitrary (Γ.CoalStrat S))⟩
  -- Sion's saddle point (X = the minimizing side, Y = the maximizing side)
  obtain ⟨a, ha, b, hb, hsaddle⟩ := Sion.exists_isSaddlePointOn
    (X := stdSimplex ℝ (Γ.CoalStrat Sᶜ)) (Y := stdSimplex ℝ (Γ.CoalStrat S))
    (f := fun x y => Γ.bilin S y x)
    (ne_X := hXne)
    (cX := convex_stdSimplex ℝ _)
    (kX := isCompact_stdSimplex ℝ _)
    (hfy := fun y _ =>
      (continuous_bilin_right Γ S y).continuousOn.lowerSemicontinuousOn)
    (hfy' := fun y _ => quasiconvexOn2_bilin Γ S y)
    (cY := convex_stdSimplex ℝ _)
    (ne_Y := hYne)
    (kY := isCompact_stdSimplex ℝ _)
    (hfx := fun x _ =>
      (continuous_bilin_left Γ S x).continuousOn.upperSemicontinuousOn)
    (hfx' := fun x _ => quasiconcave2_bilin Γ S x)
  -- boundedness facts
  have hbbdξ : ∀ ξ : stdSimplex ℝ (Γ.CoalStrat S),
      BddBelow (Set.range fun η : stdSimplex ℝ (Γ.CoalStrat Sᶜ) => Γ.bilin S (↑ξ) (↑η)) := by
    intro ξ
    refine ⟨-(∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ, |Γ.coalPayoff S τS τC|), ?_⟩
    rintro _ ⟨η, rfl⟩
    dsimp only
    have h := abs_bilin_le Γ S ξ.2 η.2
    exact (abs_le.mp h).1
  have hbbdη : ∀ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ),
      BddAbove (Set.range fun ξ : stdSimplex ℝ (Γ.CoalStrat S) => Γ.bilin S (↑ξ) (↑η)) := by
    intro η
    refine ⟨∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ, |Γ.coalPayoff S τS τC|, ?_⟩
    rintro _ ⟨ξ, rfl⟩
    dsimp only
    have h := abs_bilin_le Γ S ξ.2 η.2
    exact (abs_le.mp h).2
  have habd : BddAbove (Set.range fun ξ : stdSimplex ℝ (Γ.CoalStrat S) =>
      ⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ), Γ.bilin S (↑ξ) (↑η)) := by
    refine ⟨∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ, |Γ.coalPayoff S τS τC|, ?_⟩
    rintro _ ⟨ξ, rfl⟩
    dsimp only
    have h1 : (⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ), Γ.bilin S (↑ξ) (↑η))
        ≤ Γ.bilin S (↑ξ) a :=
      ciInf_le (hbbdξ ξ) (⟨a, ha⟩ : stdSimplex ℝ (Γ.CoalStrat Sᶜ))
    have h2 := abs_bilin_le Γ S ξ.2 ha
    exact le_trans h1 (abs_le.mp h2).2
  have hibd : BddBelow (Set.range fun η : stdSimplex ℝ (Γ.CoalStrat Sᶜ) =>
      ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat S), Γ.bilin S (↑ξ) (↑η)) := by
    refine ⟨-(∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ, |Γ.coalPayoff S τS τC|), ?_⟩
    rintro _ ⟨η, rfl⟩
    dsimp only
    have h1 : Γ.bilin S b (↑η)
        ≤ ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat S), Γ.bilin S (↑ξ) (↑η) :=
      le_ciSup (hbbdη η) (⟨b, hb⟩ : stdSimplex ℝ (Γ.CoalStrat S))
    have h2 := abs_bilin_le Γ S hb η.2
    exact le_trans (abs_le.mp h2).1 h1
  -- the two iterated optima both equal bilin S b a
  have hsupinf : (⨆ ξ : stdSimplex ℝ (Γ.CoalStrat S),
      ⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ), Γ.bilin S (↑ξ) (↑η)) = Γ.bilin S b a := by
    apply le_antisymm
    · refine ciSup_le (fun ξ => ?_)
      refine le_trans (ciInf_le (hbbdξ ξ) ⟨a, ha⟩) ?_
      exact hsaddle a ha (↑ξ) ξ.2
    · have e2 : Γ.bilin S b a
          ≤ ⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ), Γ.bilin S b (↑η) := by
        refine le_ciInf (fun η => ?_)
        have h := hsaddle (↑η) η.2 b hb
        dsimp only at h
        exact h
      have e3 : (⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ), Γ.bilin S b (↑η))
          ≤ ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat S), ⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ),
              Γ.bilin S (↑ξ) (↑η) :=
        le_ciSup habd ⟨b, hb⟩
      exact le_trans e2 e3
  have hinfSup : (⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ),
      ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat S), Γ.bilin S (↑ξ) (↑η)) = Γ.bilin S b a := by
    apply le_antisymm
    · refine le_trans (ciInf_le hibd ⟨a, ha⟩) ?_
      refine ciSup_le (fun ξ => ?_)
      exact hsaddle a ha (↑ξ) ξ.2
    · refine le_ciInf (fun η => ?_)
      have h := hsaddle (↑η) η.2 b hb
      dsimp only at h
      exact le_trans h (le_ciSup (hbbdη η) ⟨b, hb⟩)
  rw [hsupinf, hinfSup]

end Sion

section PartB

/-- Pulling a mixed strategy of `-S` back along `castE`. -/
private def pullAgg (S : Finset (Fin n)) (y : Γ.CoalStrat Sᶜᶜ → ℝ) :
    Γ.CoalStrat S → ℝ := fun x => y (castE Γ S x)

/-- The pull of an element of the simplex is in the simplex. -/
private lemma pullAgg_mem (S : Finset (Fin n)) (η' : stdSimplex ℝ (Γ.CoalStrat Sᶜᶜ)) :
    pullAgg Γ S (↑η') ∈ stdSimplex ℝ (Γ.CoalStrat S) := by
  constructor
  · intro x
    exact η'.property.1 _
  · show ∑ x : Γ.CoalStrat S, (↑η' : _ → ℝ) (castE Γ S x) = 1
    rw [Fintype.sum_equiv (castE Γ S)
      (fun x => (↑η' : _ → ℝ) (castE Γ S x)) (fun y => (↑η' : _ → ℝ) y)
      (fun _ => rfl)]
    exact simplex_sum η'

/-- The canonical bijection of the two simplices. -/
private def simplexPull (S : Finset (Fin n)) :
    (stdSimplex ℝ (Γ.CoalStrat Sᶜᶜ)) ≃ (stdSimplex ℝ (Γ.CoalStrat S)) where
  toFun η' := ⟨pullAgg Γ S (↑η'), pullAgg_mem Γ S η'⟩
  invFun a := ⟨fun y => (↑a : _ → ℝ) ((castE Γ S).symm y), by
    constructor
    · intro y
      exact a.property.1 _
    · show ∑ y : Γ.CoalStrat Sᶜᶜ, (↑a : _ → ℝ) ((castE Γ S).symm y) = 1
      rw [Fintype.sum_equiv ((castE Γ S).symm)
        (fun y => (↑a : _ → ℝ) ((castE Γ S).symm y)) (fun x => (↑a : _ → ℝ) x)
        (fun _ => rfl)]
      exact simplex_sum a⟩
  left_inv := by
    intro η'
    ext x
    rfl
  right_inv := by
    intro a
    ext x
    rfl

/-- (25:3:b): the characteristic function of the complement is the negative. -/
private lemma charFun_compl_neg (S : Finset (Fin n)) :
    Γ.charFun Sᶜ = -Γ.charFun S := by
  haveI hNS : Nonempty (Γ.CoalStrat S) := nonempty_coalStrat Γ S
  haveI hNS' : Nonempty (Γ.CoalStrat Sᶜ) := nonempty_coalStrat Γ _
  haveI hNS'' : Nonempty (Γ.CoalStrat (Sᶜ)ᶜ) := nonempty_coalStrat Γ _
  have hNX : Nonempty (stdSimplex ℝ (Γ.CoalStrat S)) := by
    exact ⟨Pi.single (Classical.arbitrary (Γ.CoalStrat S)) 1,
      single_mem_stdSimplex (𝕜 := ℝ) (Classical.arbitrary (Γ.CoalStrat S))⟩
  have hNY : Nonempty (stdSimplex ℝ (Γ.CoalStrat Sᶜ)) := by
    exact ⟨Pi.single (Classical.arbitrary (Γ.CoalStrat Sᶜ)) 1,
      single_mem_stdSimplex (𝕜 := ℝ) (Classical.arbitrary (Γ.CoalStrat Sᶜ))⟩
  have hNY' : Nonempty (stdSimplex ℝ (Γ.CoalStrat (Sᶜ)ᶜ)) := by
    exact ⟨Pi.single (Classical.arbitrary (Γ.CoalStrat (Sᶜ)ᶜ)) 1,
      single_mem_stdSimplex (𝕜 := ℝ) (Classical.arbitrary (Γ.CoalStrat (Sᶜ)ᶜ))⟩
  -- the pointwise symmetry
  have hpt : ∀ (ξ' : stdSimplex ℝ (Γ.CoalStrat Sᶜ)) (η' : stdSimplex ℝ (Γ.CoalStrat (Sᶜ)ᶜ)),
      Γ.bilin Sᶜ (↑ξ') (↑η')
        = -(Γ.bilin S (fun x => (↑η' : _ → ℝ) (castE Γ S x)) (↑ξ')) := by
    intro ξ' η'
    have hsymm : Γ.bilin Sᶜ (↑ξ')
        (fun x => (↑η' : _ → ℝ) ((castE Γ S) ((castE Γ S).symm x)))
      = -(Γ.bilin S (fun x => (↑η' : _ → ℝ) (castE Γ S x)) (↑ξ')) :=
      bilin_neg_swap Γ S (fun x => (↑η' : _ → ℝ) (castE Γ S x)) (↑ξ')
    calc Γ.bilin Sᶜ (↑ξ') (↑η')
        = Γ.bilin Sᶜ (↑ξ')
            (fun x => (↑η' : _ → ℝ) ((castE Γ S) ((castE Γ S).symm x))) := by
          rfl
      _ = -(Γ.bilin S (fun x => (↑η' : _ → ℝ) (castE Γ S x)) (↑ξ')) := hsymm


  -- the chain
  have key1 : ∀ (ξ' : stdSimplex ℝ (Γ.CoalStrat Sᶜ)),
      (⨅ η' : stdSimplex ℝ (Γ.CoalStrat (Sᶜ)ᶜ),
          Γ.bilin Sᶜ (↑ξ') (↑η'))
        = -(⨆ η' : stdSimplex ℝ (Γ.CoalStrat (Sᶜ)ᶜ),
              Γ.bilin S (fun x => (↑η' : _ → ℝ) (castE Γ S x)) (↑ξ')) := by
    intro ξ'
    rw [← iInf_neg_eq' (fun (η' : stdSimplex ℝ (Γ.CoalStrat (Sᶜ)ᶜ)) =>
      Γ.bilin S (fun x => (↑η' : _ → ℝ) (castE Γ S x)) (↑ξ'))]
    exact congrArg iInf (funext (fun η' => hpt ξ' η'))
  have key2 : (⨆ (ξ' : stdSimplex ℝ (Γ.CoalStrat Sᶜ)),
          ⨅ η' : stdSimplex ℝ (Γ.CoalStrat (Sᶜ)ᶜ), Γ.bilin Sᶜ (↑ξ') (↑η'))
      = -(⨅ (ξ' : stdSimplex ℝ (Γ.CoalStrat Sᶜ)),
            ⨆ η' : stdSimplex ℝ (Γ.CoalStrat (Sᶜ)ᶜ),
              Γ.bilin S (fun x => (↑η' : _ → ℝ) (castE Γ S x)) (↑ξ')) := by
    rw [congrArg iSup (funext (fun ξ' => key1 ξ'))]
    exact iSup_neg_eq' (fun (ξ' : stdSimplex ℝ (Γ.CoalStrat Sᶜ)) =>
      ⨆ η' : stdSimplex ℝ (Γ.CoalStrat (Sᶜ)ᶜ),
        Γ.bilin S (fun x => (↑η' : _ → ℝ) (castE Γ S x)) (↑ξ'))
  have key3 : ∀ (ξ' : stdSimplex ℝ (Γ.CoalStrat Sᶜ)),
      (⨆ η' : stdSimplex ℝ (Γ.CoalStrat (Sᶜ)ᶜ),
          Γ.bilin S (fun x => (↑η' : _ → ℝ) (castE Γ S x)) (↑ξ'))
        = ⨆ a : stdSimplex ℝ (Γ.CoalStrat S), Γ.bilin S (↑a) (↑ξ') := by
    intro ξ'
    calc (⨆ η' : stdSimplex ℝ (Γ.CoalStrat (Sᶜ)ᶜ),
            Γ.bilin S (fun x => (↑η' : _ → ℝ) (castE Γ S x)) (↑ξ'))
        = ⨆ η' : stdSimplex ℝ (Γ.CoalStrat (Sᶜ)ᶜ),
              Γ.bilin S (↑(simplexPull Γ S η')) (↑ξ') := by
          exact congrArg iSup (funext (fun η' => by
            show Γ.bilin S (fun x => (↑η' : _ → ℝ) (castE Γ S x)) (↑ξ')
                = Γ.bilin S (↑(simplexPull Γ S η')) (↑ξ')
            rfl))
      _ = ⨆ a : stdSimplex ℝ (Γ.CoalStrat S), Γ.bilin S (↑a) (↑ξ') :=
          (iSup_bij (simplexPull Γ S)
            (fun a => Γ.bilin S (↑a) (↑ξ'))).symm
  calc Γ.charFun Sᶜ
      = ⨆ ξ' : stdSimplex ℝ (Γ.CoalStrat Sᶜ),
          ⨅ η' : stdSimplex ℝ (Γ.CoalStrat (Sᶜ)ᶜ), Γ.bilin Sᶜ (↑ξ') (↑η') := rfl
    _ = -(⨅ (ξ' : stdSimplex ℝ (Γ.CoalStrat Sᶜ)),
          ⨆ a : stdSimplex ℝ (Γ.CoalStrat S), Γ.bilin S (↑a) (↑ξ')) := by
        rw [key2, congrArg (fun t => -t) (congrArg iInf (funext (fun ξ' => key3 ξ')))]
    _ = -(Γ.charFun S) := by
        rw [show Γ.charFun S = ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat S),
              ⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ), Γ.bilin S (↑ξ) (↑η) from rfl,
            sion_bilin Γ S]

end PartB

section PartC

variable (Γ : ZeroSumGame n)

/-- Restriction of an `S ∪ T`-aggregate to `S`. -/
private def toSAgg (S T : Finset (Fin n)) (τ : Γ.CoalStrat (S ∪ T)) : Γ.CoalStrat S :=
  fun k => τ ⟨(k : Fin n), Finset.mem_union_left T k.2⟩

/-- Restriction of an `S ∪ T`-aggregate to `T`. -/
private def toTAgg (S T : Finset (Fin n)) (τ : Γ.CoalStrat (S ∪ T)) : Γ.CoalStrat T :=
  fun k => τ ⟨(k : Fin n), Finset.mem_union_right S k.2⟩

/-- Gluing an `S`-aggregate and a `T`-aggregate (disjoint case). -/
private def fromSTAgg (S T : Finset (Fin n)) (a : Γ.CoalStrat S) (b : Γ.CoalStrat T) :
    Γ.CoalStrat (S ∪ T) :=
  fun k => if h : (k : Fin n) ∈ S then a ⟨(k : Fin n), h⟩
    else b ⟨(k : Fin n), (Finset.mem_union.mp k.2).resolve_left h⟩

/-- The product equivalence of the aggregate sets (disjoint case). -/
private def prodAggEquiv (S T : Finset (Fin n)) (hST : Disjoint S T) :
    Γ.CoalStrat (S ∪ T) ≃ Γ.CoalStrat S × Γ.CoalStrat T where
  toFun τ := (toSAgg Γ S T τ, toTAgg Γ S T τ)
  invFun p := fromSTAgg Γ S T p.1 p.2
  left_inv := by
    intro τ
    funext k
    by_cases h : (k : Fin n) ∈ S <;> simp [fromSTAgg, toSAgg, toTAgg, h]
  right_inv := by
    intro p
    obtain ⟨a, b⟩ := p
    refine Prod.ext (by funext k; simp [fromSTAgg, toSAgg]) (by
      funext k
      have hns : ¬((k : Fin n) ∈ S) := fun hs =>
        absurd (hST.le_bot (Finset.mem_inter.2 ⟨hs, k.2⟩)) (by simp)
      simp [fromSTAgg, toTAgg, hns])

/-- Assembling an `Sᶜ`-aggregate from a `T`-aggregate and an `(S ∪ T)ᶜ`-aggregate. -/
private def glueSC (S T : Finset (Fin n)) (b : Γ.CoalStrat T) (c : Γ.CoalStrat ((S ∪ T)ᶜ)) :
    Γ.CoalStrat (Sᶜ) :=
  fun k => if h : (k : Fin n) ∈ T then b ⟨(k : Fin n), h⟩
    else c ⟨(k : Fin n), Finset.mem_compl.mpr fun hmem => by
      rcases Finset.mem_union.mp hmem with hs | ht
      · exact (Finset.mem_compl.mp k.2) hs
      · exact absurd ht h⟩

/-- The equivalence `CoalStrat T × CoalStrat (S∪T)ᶜ ≃ CoalStrat Sᶜ`. -/
private def complEquiv1 (S T : Finset (Fin n)) (hST : Disjoint S T) :
    Γ.CoalStrat T × Γ.CoalStrat ((S ∪ T)ᶜ) ≃ Γ.CoalStrat (Sᶜ) where
  toFun p := glueSC Γ S T p.1 p.2
  invFun σ :=
    (fun k => σ ⟨(k : Fin n), Finset.mem_compl.mpr fun hs =>
      absurd (hST.le_bot (Finset.mem_inter.2 ⟨hs, k.2⟩)) (by simp)⟩,
    fun k => σ ⟨(k : Fin n), Finset.mem_compl.mpr fun hs =>
      (Finset.mem_compl.mp k.2) (Finset.mem_union.2 (Or.inl hs))⟩)
  left_inv := by
    intro p
    obtain ⟨b, c⟩ := p
    refine Prod.ext (by
      funext k
      simp [glueSC]) (by
      funext k
      have hnt : ¬((k : Fin n) ∈ T) := fun ht =>
        absurd ((Finset.mem_compl.mp k.2) (Finset.mem_union.2 (Or.inr ht))) (by simp)
      simp [glueSC, hnt])
  right_inv := by
    intro σ
    funext k
    by_cases h : (k : Fin n) ∈ T <;> simp [glueSC, h]

/-- Assembling a `Tᶜ`-aggregate from an `S`-aggregate and an `(S ∪ T)ᶜ`-aggregate. -/
private def glueTC (S T : Finset (Fin n)) (a : Γ.CoalStrat S) (c : Γ.CoalStrat ((S ∪ T)ᶜ)) :
    Γ.CoalStrat (Tᶜ) :=
  fun k => if h : (k : Fin n) ∈ S then a ⟨(k : Fin n), h⟩
    else c ⟨(k : Fin n), Finset.mem_compl.mpr fun hmem => by
      rcases Finset.mem_union.mp hmem with hs | ht
      · exact absurd hs h
      · exact (Finset.mem_compl.mp k.2) ht⟩

/-- The equivalence `CoalStrat S × CoalStrat (S∪T)ᶜ ≃ CoalStrat Tᶜ`. -/
private def complEquiv2 (S T : Finset (Fin n)) (hST : Disjoint S T) :
    Γ.CoalStrat S × Γ.CoalStrat ((S ∪ T)ᶜ) ≃ Γ.CoalStrat (Tᶜ) where
  toFun p := glueTC Γ S T p.1 p.2
  invFun σ :=
    (fun k => σ ⟨(k : Fin n), Finset.mem_compl.mpr fun ht =>
      absurd (hST.le_bot (Finset.mem_inter.2 ⟨k.2, ht⟩)) (by simp)⟩,
    fun k => σ ⟨(k : Fin n), Finset.mem_compl.mpr fun ht =>
      (Finset.mem_compl.mp k.2) (Finset.mem_union.2 (Or.inr ht))⟩)
  left_inv := by
    intro p
    obtain ⟨a, c⟩ := p
    refine Prod.ext (by
      funext k
      simp [glueTC]) (by
      funext k
      have hns : ¬((k : Fin n) ∈ S) := fun hs =>
        absurd (Finset.mem_compl.mp k.2 (Finset.mem_union.2 (Or.inl hs))) (by simp)
      simp [glueTC, hns])
  right_inv := by
    intro σ
    funext k
    by_cases h : (k : Fin n) ∈ S <;> simp [glueTC, h]

/-- The profiles of `S ∪ T` and of `S` (with the complement split at `T`) agree. -/
private lemma joint_union_S (S T : Finset (Fin n))
    (τST : Γ.CoalStrat (S ∪ T)) (τC : Γ.CoalStrat ((S ∪ T)ᶜ)) :
    Γ.joint (S ∪ T) τST τC
      = Γ.joint S (toSAgg Γ S T τST) (glueSC Γ S T (toTAgg Γ S T τST) τC) := by
  funext k
  by_cases hS : k ∈ S
  · simp only [TheoryOfGames.CharFun.ZeroSumGame.joint, toSAgg,
      dif_pos (Finset.mem_union.2 (Or.inl hS)), dif_pos hS]
  · by_cases hT : k ∈ T
    · simp only [TheoryOfGames.CharFun.ZeroSumGame.joint, toSAgg, toTAgg, glueSC,
        dif_pos (Finset.mem_union.2 (Or.inr hT)), dif_neg hS, dif_pos hT]
    · have hnu : ¬ k ∈ S ∪ T := by
        intro hmem
        rcases Finset.mem_union.mp hmem with hs | ht
        · exact hS hs
        · exact hT ht
      simp only [TheoryOfGames.CharFun.ZeroSumGame.joint, toSAgg, toTAgg, glueSC,
        dif_neg hnu, dif_neg hS, dif_neg hT]

/-- The profiles of `S ∪ T` and of `T` (with the complement split at `S`) agree. -/
private lemma joint_union_T (S T : Finset (Fin n))
    (τST : Γ.CoalStrat (S ∪ T)) (τC : Γ.CoalStrat ((S ∪ T)ᶜ)) :
    Γ.joint (S ∪ T) τST τC
      = Γ.joint T (toTAgg Γ S T τST) (glueTC Γ S T (toSAgg Γ S T τST) τC) := by
  funext k
  by_cases hT : k ∈ T
  · simp only [TheoryOfGames.CharFun.ZeroSumGame.joint, toTAgg,
      dif_pos (Finset.mem_union.2 (Or.inr hT)), dif_pos hT]
  · by_cases hS : k ∈ S
    · simp only [TheoryOfGames.CharFun.ZeroSumGame.joint, toSAgg, toTAgg, glueTC,
        dif_pos (Finset.mem_union.2 (Or.inl hS)), dif_neg hT, dif_pos hS]
    · have hnu : ¬ k ∈ S ∪ T := by
        intro hmem
        rcases Finset.mem_union.mp hmem with hs | ht
        · exact hS hs
        · exact hT ht
      simp only [TheoryOfGames.CharFun.ZeroSumGame.joint, toSAgg, toTAgg, glueTC,
        dif_neg hnu, dif_neg hT, dif_neg hS]

/-- The payoff decomposition underlying (25:3:c): the payoff of `S ∪ T` splits along the
disjoint parts. -/
private lemma coalPayoff_union (S T : Finset (Fin n)) (hST : Disjoint S T)
    (τST : Γ.CoalStrat (S ∪ T)) (τC : Γ.CoalStrat ((S ∪ T)ᶜ)) :
    Γ.coalPayoff (S ∪ T) τST τC
      = Γ.coalPayoff S (toSAgg Γ S T τST) (glueSC Γ S T (toTAgg Γ S T τST) τC)
        + Γ.coalPayoff T (toTAgg Γ S T τST) (glueTC Γ S T (toSAgg Γ S T τST) τC) := by
  show ∑ k ∈ S ∪ T, Γ.H (Γ.joint (S ∪ T) τST τC) k = _
  rw [Finset.sum_union hST]
  nth_rewrite 1 [joint_union_S Γ S T τST τC]
  rw [joint_union_T Γ S T τST τC]
  rfl

/-- Splitting a product-indexed sum (first-order bridge over `Fintype.sum_prod_type`). -/
private lemma sps {A B : Type} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    ∑ p : A × B, f p = ∑ a : A, ∑ b : B, f (a, b) := Fintype.sum_prod_type f

/-- Merging a double sum into a product-indexed sum. -/
private lemma spm {A B : Type} [Fintype A] [Fintype B] (f : A → B → ℝ) :
    ∑ a : A, ∑ b : B, f a b = ∑ p : A × B, f p.1 p.2 :=
  (Fintype.sum_prod_type' f).symm

/-- Marginalization of a triple product weight. -/
private lemma sum_marginal {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (wA : A → ℝ) (wB : B → ℝ) (wC : C → ℝ) (F : A → B → C → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c * (wA a * wB b) * wC c
      = ∑ a, wA a * ∑ b, ∑ c, F a b c * (wB b * wC c) := by
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring

/-- Marginalization with the outer weight on the second binder. -/
private lemma sum_marginal2 {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (wA : A → ℝ) (wB : B → ℝ) (wC : C → ℝ) (F : B → A → C → ℝ) :
    ∑ b, ∑ a, ∑ c, F b a c * (wA a * wB b) * wC c
      = ∑ b, wB b * ∑ a, ∑ c, F b a c * (wA a * wC c) := by
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

/-- (25:3:c): superadditivity on disjoint coalitions. -/
private lemma charFun_union_ge (S T : Finset (Fin n)) (hST : Disjoint S T) :
    Γ.charFun S + Γ.charFun T ≤ Γ.charFun (S ∪ T) := by
  classical
  haveI hNS : Nonempty (Γ.CoalStrat S) := nonempty_coalStrat Γ S
  haveI hNT : Nonempty (Γ.CoalStrat T) := nonempty_coalStrat Γ T
  haveI hNU : Nonempty (Γ.CoalStrat (S ∪ T)) := nonempty_coalStrat Γ _
  haveI hNC : Nonempty (Γ.CoalStrat (S ∪ T)ᶜ) := nonempty_coalStrat Γ _
  haveI hNX : Nonempty (stdSimplex ℝ (Γ.CoalStrat S)) := nonempty_simplex
  haveI hNY : Nonempty (stdSimplex ℝ (Γ.CoalStrat T)) := nonempty_simplex
  haveI hNZ : Nonempty (stdSimplex ℝ (Γ.CoalStrat (S ∪ T)ᶜ)) := nonempty_simplex
  haveI hNW : Nonempty (stdSimplex ℝ (Γ.CoalStrat (S ∪ T))) := nonempty_simplex
  by_contra hlt
  push_neg at hlt
  set eps : ℝ := (Γ.charFun S + Γ.charFun T - Γ.charFun (S ∪ T)) / 3 with heps
  have h3 : Γ.charFun S + Γ.charFun T - Γ.charFun (S ∪ T) = 3 * eps := by
    rw [heps]; ring
  have heps0 : 0 < eps := by rw [heps]; exact div_pos (by linarith) three_pos
  have hcfS : Γ.charFun S = ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat S),
      ⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ), Γ.bilin S (↑ξ) (↑η) := rfl
  have hcfT : Γ.charFun T = ⨆ ζ : stdSimplex ℝ (Γ.CoalStrat T),
      ⨅ ρ : stdSimplex ℝ (Γ.CoalStrat Tᶜ), Γ.bilin T (↑ζ) (↑ρ) := rfl
  have hcfU : Γ.charFun (S ∪ T) = ⨆ ω : stdSimplex ℝ (Γ.CoalStrat (S ∪ T)),
      ⨅ η : stdSimplex ℝ (Γ.CoalStrat (S ∪ T)ᶜ), Γ.bilin (S ∪ T) (↑ω) (↑η) := rfl
  obtain ⟨ξ, hξ⟩ := exists_lt_of_lt_ciSup (b := Γ.charFun S - eps)
    (f := fun ξ : stdSimplex ℝ (Γ.CoalStrat S) =>
      ⨅ η : stdSimplex ℝ (Γ.CoalStrat Sᶜ), Γ.bilin S (↑ξ) (↑η))
    (by rw [hcfS]; linarith)
  obtain ⟨ζ, hζ⟩ := exists_lt_of_lt_ciSup (b := Γ.charFun T - eps)
    (f := fun ζ : stdSimplex ℝ (Γ.CoalStrat T) =>
      ⨅ ρ : stdSimplex ℝ (Γ.CoalStrat Tᶜ), Γ.bilin T (↑ζ) (↑ρ))
    (by rw [hcfT]; linarith)
  -- boundedness facts
  have hbdSξ : BddBelow (Set.range
      fun μ : stdSimplex ℝ (Γ.CoalStrat Sᶜ) => Γ.bilin S (↑ξ) (↑μ)) := by
    refine ⟨-(∑ τS : Γ.CoalStrat S, ∑ τC : Γ.CoalStrat Sᶜ, |Γ.coalPayoff S τS τC|), ?_⟩
    rintro _ ⟨μ, rfl⟩
    dsimp only
    have h := abs_bilin_le Γ S ξ.2 μ.2
    exact (abs_le.mp h).1
  have hbdTζ : BddBelow (Set.range
      fun μ : stdSimplex ℝ (Γ.CoalStrat Tᶜ) => Γ.bilin T (↑ζ) (↑μ)) := by
    refine ⟨-(∑ τS : Γ.CoalStrat T, ∑ τC : Γ.CoalStrat Tᶜ, |Γ.coalPayoff T τS τC|), ?_⟩
    rintro _ ⟨μ, rfl⟩
    dsimp only
    have h := abs_bilin_le Γ T ζ.2 μ.2
    exact (abs_le.mp h).1
  have hbdU : ∀ ω : stdSimplex ℝ (Γ.CoalStrat (S ∪ T)),
      BddBelow (Set.range fun η : stdSimplex ℝ (Γ.CoalStrat (S ∪ T)ᶜ) =>
        Γ.bilin (S ∪ T) (↑ω) (↑η)) := by
    intro ω
    refine ⟨-(∑ τS : Γ.CoalStrat (S ∪ T), ∑ τC : Γ.CoalStrat (S ∪ T)ᶜ,
      |Γ.coalPayoff (S ∪ T) τS τC|), ?_⟩
    rintro _ ⟨η, rfl⟩
    dsimp only
    have h := abs_bilin_le Γ (S ∪ T) ω.2 η.2
    exact (abs_le.mp h).1
  have hbdUU : BddAbove (Set.range fun ω : stdSimplex ℝ (Γ.CoalStrat (S ∪ T)) =>
      ⨅ η : stdSimplex ℝ (Γ.CoalStrat (S ∪ T)ᶜ), Γ.bilin (S ∪ T) (↑ω) (↑η)) := by
    refine ⟨∑ τS : Γ.CoalStrat (S ∪ T), ∑ τC : Γ.CoalStrat (S ∪ T)ᶜ,
      |Γ.coalPayoff (S ∪ T) τS τC|, ?_⟩
    rintro _ ⟨ω, rfl⟩
    dsimp only
    have h1 := ciInf_le (hbdU ω)
      (Classical.arbitrary (stdSimplex ℝ (Γ.CoalStrat (S ∪ T)ᶜ)))
    have h2 := abs_bilin_le Γ (S ∪ T) ω.2
      (Classical.arbitrary (stdSimplex ℝ (Γ.CoalStrat (S ∪ T)ᶜ))).2
    exact le_trans h1 (abs_le.mp h2).2
  -- membership of the product weight
  have hprodmem : (fun τST : Γ.CoalStrat (S ∪ T) => (ξ : Γ.CoalStrat S → ℝ) (toSAgg Γ S T τST) * (ζ : Γ.CoalStrat T → ℝ) (toTAgg Γ S T τST)) ∈ stdSimplex ℝ (Γ.CoalStrat (S ∪ T)) := by
    refine ⟨fun τST => mul_nonneg ((mem_Icc_of_mem_stdSimplex ξ.2 _).1)
      ((mem_Icc_of_mem_stdSimplex ζ.2 _).1), ?_⟩
    rw [Fintype.sum_equiv (prodAggEquiv Γ S T hST)
      (f := fun τST : Γ.CoalStrat (S ∪ T) =>
        (ξ : Γ.CoalStrat S → ℝ) (toSAgg Γ S T τST)
          * (ζ : Γ.CoalStrat T → ℝ) (toTAgg Γ S T τST))
      (g := fun p : Γ.CoalStrat S × Γ.CoalStrat T =>
        (ξ : Γ.CoalStrat S → ℝ) p.1 * (ζ : Γ.CoalStrat T → ℝ) p.2)
      (fun τST => show (ξ : Γ.CoalStrat S → ℝ) (toSAgg Γ S T τST)
          * (ζ : Γ.CoalStrat T → ℝ) (toTAgg Γ S T τST)
        = (ξ : Γ.CoalStrat S → ℝ) ((prodAggEquiv Γ S T hST) τST).1
          * (ζ : Γ.CoalStrat T → ℝ) ((prodAggEquiv Γ S T hST) τST).2 from rfl),
      sps (f := fun p : Γ.CoalStrat S × Γ.CoalStrat T =>
        (ξ : Γ.CoalStrat S → ℝ) p.1 * (ζ : Γ.CoalStrat T → ℝ) p.2)]
    simp only [← Finset.mul_sum]
    rw [simplex_sum ζ]
    simp only [mul_one]
    exact simplex_sum ξ
  -- membership of the marginals
  have hμ₁mem : ∀ η : stdSimplex ℝ (Γ.CoalStrat ((S ∪ T)ᶜ)),
      (fun σ : Γ.CoalStrat (Sᶜ) => (ζ : Γ.CoalStrat T → ℝ) ((complEquiv1 Γ S T hST).symm σ).1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv1 Γ S T hST).symm σ).2) ∈ stdSimplex ℝ (Γ.CoalStrat (Sᶜ)) := by
    intro η
    refine ⟨fun σ => mul_nonneg ((mem_Icc_of_mem_stdSimplex ζ.2 _).1)
      ((mem_Icc_of_mem_stdSimplex η.2 _).1), ?_⟩
    rw [Fintype.sum_equiv ((complEquiv1 Γ S T hST).symm)
      (f := fun σ : Γ.CoalStrat (Sᶜ) =>
        (ζ : Γ.CoalStrat T → ℝ) ((complEquiv1 Γ S T hST).symm σ).1
          * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv1 Γ S T hST).symm σ).2)
      (g := fun p : Γ.CoalStrat T × Γ.CoalStrat ((S ∪ T)ᶜ) =>
        (ζ : Γ.CoalStrat T → ℝ) p.1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) p.2)
      (fun _ => rfl),
      sps (f := fun p : Γ.CoalStrat T × Γ.CoalStrat ((S ∪ T)ᶜ) =>
        (ζ : Γ.CoalStrat T → ℝ) p.1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) p.2)]
    simp only [← Finset.mul_sum]
    rw [simplex_sum η]
    simp only [mul_one]
    exact simplex_sum ζ
  have hμ₂mem : ∀ η : stdSimplex ℝ (Γ.CoalStrat ((S ∪ T)ᶜ)),
      (fun ρ : Γ.CoalStrat (Tᶜ) => (ξ : Γ.CoalStrat S → ℝ) ((complEquiv2 Γ S T hST).symm ρ).1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv2 Γ S T hST).symm ρ).2) ∈ stdSimplex ℝ (Γ.CoalStrat (Tᶜ)) := by
    intro η
    refine ⟨fun ρ => mul_nonneg ((mem_Icc_of_mem_stdSimplex ξ.2 _).1)
      ((mem_Icc_of_mem_stdSimplex η.2 _).1), ?_⟩
    rw [Fintype.sum_equiv ((complEquiv2 Γ S T hST).symm)
      (f := fun ρ : Γ.CoalStrat (Tᶜ) =>
        (ξ : Γ.CoalStrat S → ℝ) ((complEquiv2 Γ S T hST).symm ρ).1
          * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv2 Γ S T hST).symm ρ).2)
      (g := fun p : Γ.CoalStrat S × Γ.CoalStrat ((S ∪ T)ᶜ) =>
        (ξ : Γ.CoalStrat S → ℝ) p.1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) p.2)
      (fun _ => rfl),
      sps (f := fun p : Γ.CoalStrat S × Γ.CoalStrat ((S ∪ T)ᶜ) =>
        (ξ : Γ.CoalStrat S → ℝ) p.1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) p.2)]
    simp only [← Finset.mul_sum]
    rw [simplex_sum η]
    simp only [mul_one]
    exact simplex_sum ξ
  -- the marginalization identity
  have master : ∀ η : stdSimplex ℝ (Γ.CoalStrat ((S ∪ T)ᶜ)),
      Γ.bilin (S ∪ T) (fun τST : Γ.CoalStrat (S ∪ T) => (ξ : Γ.CoalStrat S → ℝ) (toSAgg Γ S T τST) * (ζ : Γ.CoalStrat T → ℝ) (toTAgg Γ S T τST)) (↑η)
        = Γ.bilin S (↑ξ) (fun σ : Γ.CoalStrat (Sᶜ) => (ζ : Γ.CoalStrat T → ℝ) ((complEquiv1 Γ S T hST).symm σ).1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv1 Γ S T hST).symm σ).2) + Γ.bilin T (↑ζ) (fun ρ : Γ.CoalStrat (Tᶜ) => (ξ : Γ.CoalStrat S → ℝ) ((complEquiv2 Γ S T hST).symm ρ).1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv2 Γ S T hST).symm ρ).2) := by
    intro η
    show (∑ τST : Γ.CoalStrat (S ∪ T), ∑ τC : Γ.CoalStrat (S ∪ T)ᶜ,
        Γ.coalPayoff (S ∪ T) τST τC * ((ξ : Γ.CoalStrat S → ℝ) (toSAgg Γ S T τST)
          * (ζ : Γ.CoalStrat T → ℝ) (toTAgg Γ S T τST))
          * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) τC) = _
    have hterm : ∀ (τST : Γ.CoalStrat (S ∪ T)) (τC : Γ.CoalStrat (S ∪ T)ᶜ),
        Γ.coalPayoff (S ∪ T) τST τC * ((ξ : Γ.CoalStrat S → ℝ) (toSAgg Γ S T τST)
          * (ζ : Γ.CoalStrat T → ℝ) (toTAgg Γ S T τST))
          * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) τC
        = Γ.coalPayoff S (toSAgg Γ S T τST) (glueSC Γ S T (toTAgg Γ S T τST) τC)
            * ((ξ : Γ.CoalStrat S → ℝ) (toSAgg Γ S T τST)
              * (ζ : Γ.CoalStrat T → ℝ) (toTAgg Γ S T τST))
            * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) τC
          + Γ.coalPayoff T (toTAgg Γ S T τST) (glueTC Γ S T (toSAgg Γ S T τST) τC)
            * ((ξ : Γ.CoalStrat S → ℝ) (toSAgg Γ S T τST)
              * (ζ : Γ.CoalStrat T → ℝ) (toTAgg Γ S T τST))
            * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) τC := by
      intro τST τC
      rw [coalPayoff_union Γ S T hST τST τC]
      ring
    rw [Finset.sum_congr rfl (fun τST (_ : τST ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun τC (_ : τC ∈ Finset.univ) => hterm τST τC))]
    simp only [Finset.sum_add_distrib]
    -- the S part
    have hS : (∑ τST : Γ.CoalStrat (S ∪ T), ∑ τC : Γ.CoalStrat (S ∪ T)ᶜ,
        Γ.coalPayoff S (toSAgg Γ S T τST) (glueSC Γ S T (toTAgg Γ S T τST) τC)
          * ((ξ : Γ.CoalStrat S → ℝ) (toSAgg Γ S T τST)
            * (ζ : Γ.CoalStrat T → ℝ) (toTAgg Γ S T τST))
          * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) τC) = (∑ a : Γ.CoalStrat S, ∑ σ : Γ.CoalStrat (Sᶜ), Γ.coalPayoff S a σ * (ξ : Γ.CoalStrat S → ℝ) a
            * ((ζ : Γ.CoalStrat T → ℝ) ((complEquiv1 Γ S T hST).symm σ).1
              * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv1 Γ S T hST).symm σ).2)) := by
      rw [Fintype.sum_equiv (prodAggEquiv Γ S T hST)
        (f := fun τST : Γ.CoalStrat (S ∪ T) => ∑ τC : Γ.CoalStrat (S ∪ T)ᶜ,
          Γ.coalPayoff S (toSAgg Γ S T τST) (glueSC Γ S T (toTAgg Γ S T τST) τC)
            * ((ξ : Γ.CoalStrat S → ℝ) (toSAgg Γ S T τST)
              * (ζ : Γ.CoalStrat T → ℝ) (toTAgg Γ S T τST))
            * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) τC)
        (g := fun p : Γ.CoalStrat S × Γ.CoalStrat T =>
          ∑ τC : Γ.CoalStrat (S ∪ T)ᶜ,
          Γ.coalPayoff S p.1 (glueSC Γ S T p.2 τC)
            * ((ξ : Γ.CoalStrat S → ℝ) p.1 * (ζ : Γ.CoalStrat T → ℝ) p.2)
            * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) τC)
        (fun _ => rfl),
        sps (f := fun p : Γ.CoalStrat S × Γ.CoalStrat T =>
          ∑ τC : Γ.CoalStrat (S ∪ T)ᶜ,
          Γ.coalPayoff S p.1 (glueSC Γ S T p.2 τC)
            * ((ξ : Γ.CoalStrat S → ℝ) p.1 * (ζ : Γ.CoalStrat T → ℝ) p.2)
            * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) τC)]
      dsimp only
      rw [sum_marginal ((ξ : Γ.CoalStrat S → ℝ)) ((ζ : Γ.CoalStrat T → ℝ))
          ((η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ))
          (fun a b c => Γ.coalPayoff S a (glueSC Γ S T b c))]
      have hinner : ∀ a : Γ.CoalStrat S,
          (∑ b : Γ.CoalStrat T, ∑ c : Γ.CoalStrat ((S ∪ T)ᶜ),
            Γ.coalPayoff S a (glueSC Γ S T b c)
              * ((ζ : Γ.CoalStrat T → ℝ) b * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) c))
          = ∑ σ : Γ.CoalStrat (Sᶜ),
            Γ.coalPayoff S a σ
              * ((ζ : Γ.CoalStrat T → ℝ) ((complEquiv1 Γ S T hST).symm σ).1
                * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ)
                  ((complEquiv1 Γ S T hST).symm σ).2) := by
        intro a
        rw [spm (f := fun b c => Γ.coalPayoff S a (glueSC Γ S T b c)
            * ((ζ : Γ.CoalStrat T → ℝ) b * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) c)),
          Fintype.sum_equiv (complEquiv1 Γ S T hST)
            (f := fun p : Γ.CoalStrat T × Γ.CoalStrat ((S ∪ T)ᶜ) =>
              Γ.coalPayoff S a (glueSC Γ S T p.1 p.2)
                * ((ζ : Γ.CoalStrat T → ℝ) p.1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) p.2))
            (g := fun σ : Γ.CoalStrat (Sᶜ) =>
              Γ.coalPayoff S a σ
                * ((ζ : Γ.CoalStrat T → ℝ) ((complEquiv1 Γ S T hST).symm σ).1
                  * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ)
                    ((complEquiv1 Γ S T hST).symm σ).2))
            (fun p => by rw [Equiv.symm_apply_apply]; rfl)]
      simp only [hinner]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ =>
        Finset.sum_congr rfl fun σ _ => by ring
    -- the T part
    have hT : (∑ τST : Γ.CoalStrat (S ∪ T), ∑ τC : Γ.CoalStrat (S ∪ T)ᶜ,
        Γ.coalPayoff T (toTAgg Γ S T τST) (glueTC Γ S T (toSAgg Γ S T τST) τC)
          * ((ξ : Γ.CoalStrat S → ℝ) (toSAgg Γ S T τST)
            * (ζ : Γ.CoalStrat T → ℝ) (toTAgg Γ S T τST))
          * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) τC) = (∑ b : Γ.CoalStrat T, ∑ ρ : Γ.CoalStrat (Tᶜ), Γ.coalPayoff T b ρ * (ζ : Γ.CoalStrat T → ℝ) b
            * ((ξ : Γ.CoalStrat S → ℝ) ((complEquiv2 Γ S T hST).symm ρ).1
              * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv2 Γ S T hST).symm ρ).2)) := by
      rw [Fintype.sum_equiv (prodAggEquiv Γ S T hST)
        (f := fun τST : Γ.CoalStrat (S ∪ T) => ∑ τC : Γ.CoalStrat (S ∪ T)ᶜ,
          Γ.coalPayoff T (toTAgg Γ S T τST) (glueTC Γ S T (toSAgg Γ S T τST) τC)
            * ((ξ : Γ.CoalStrat S → ℝ) (toSAgg Γ S T τST)
              * (ζ : Γ.CoalStrat T → ℝ) (toTAgg Γ S T τST))
            * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) τC)
        (g := fun p : Γ.CoalStrat S × Γ.CoalStrat T =>
          ∑ τC : Γ.CoalStrat (S ∪ T)ᶜ,
          Γ.coalPayoff T p.2 (glueTC Γ S T p.1 τC)
            * ((ξ : Γ.CoalStrat S → ℝ) p.1 * (ζ : Γ.CoalStrat T → ℝ) p.2)
            * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) τC)
        (fun _ => rfl),
        sps (f := fun p : Γ.CoalStrat S × Γ.CoalStrat T =>
          ∑ τC : Γ.CoalStrat (S ∪ T)ᶜ,
          Γ.coalPayoff T p.2 (glueTC Γ S T p.1 τC)
            * ((ξ : Γ.CoalStrat S → ℝ) p.1 * (ζ : Γ.CoalStrat T → ℝ) p.2)
            * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) τC)]
      dsimp only
      rw [Finset.sum_comm]
      rw [sum_marginal2 ((ξ : Γ.CoalStrat S → ℝ)) ((ζ : Γ.CoalStrat T → ℝ))
          ((η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ))
          (fun b a c => Γ.coalPayoff T b (glueTC Γ S T a c))]
      have hinner : ∀ b : Γ.CoalStrat T,
          (∑ a : Γ.CoalStrat S, ∑ c : Γ.CoalStrat ((S ∪ T)ᶜ),
            Γ.coalPayoff T b (glueTC Γ S T a c)
              * ((ξ : Γ.CoalStrat S → ℝ) a * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) c))
          = ∑ ρ : Γ.CoalStrat (Tᶜ),
            Γ.coalPayoff T b ρ
              * ((ξ : Γ.CoalStrat S → ℝ) ((complEquiv2 Γ S T hST).symm ρ).1
                * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ)
                  ((complEquiv2 Γ S T hST).symm ρ).2) := by
        intro b
        rw [spm (f := fun a c => Γ.coalPayoff T b (glueTC Γ S T a c)
            * ((ξ : Γ.CoalStrat S → ℝ) a * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) c)),
          Fintype.sum_equiv (complEquiv2 Γ S T hST)
            (f := fun p : Γ.CoalStrat S × Γ.CoalStrat ((S ∪ T)ᶜ) =>
              Γ.coalPayoff T b (glueTC Γ S T p.1 p.2)
                * ((ξ : Γ.CoalStrat S → ℝ) p.1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) p.2))
            (g := fun ρ : Γ.CoalStrat (Tᶜ) =>
              Γ.coalPayoff T b ρ
                * ((ξ : Γ.CoalStrat S → ℝ) ((complEquiv2 Γ S T hST).symm ρ).1
                  * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ)
                    ((complEquiv2 Γ S T hST).symm ρ).2))
            (fun p => by rw [Equiv.symm_apply_apply]; rfl)]
      simp only [hinner]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun ρ _ => by ring
    have hbil1 : Γ.bilin S (↑ξ) (fun σ : Γ.CoalStrat (Sᶜ) => (ζ : Γ.CoalStrat T → ℝ) ((complEquiv1 Γ S T hST).symm σ).1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv1 Γ S T hST).symm σ).2) = (∑ a : Γ.CoalStrat S, ∑ σ : Γ.CoalStrat (Sᶜ), Γ.coalPayoff S a σ * (ξ : Γ.CoalStrat S → ℝ) a
            * ((ζ : Γ.CoalStrat T → ℝ) ((complEquiv1 Γ S T hST).symm σ).1
              * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv1 Γ S T hST).symm σ).2)) := rfl
    have hbil2 : Γ.bilin T (↑ζ) (fun ρ : Γ.CoalStrat (Tᶜ) => (ξ : Γ.CoalStrat S → ℝ) ((complEquiv2 Γ S T hST).symm ρ).1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv2 Γ S T hST).symm ρ).2) = (∑ b : Γ.CoalStrat T, ∑ ρ : Γ.CoalStrat (Tᶜ), Γ.coalPayoff T b ρ * (ζ : Γ.CoalStrat T → ℝ) b
            * ((ξ : Γ.CoalStrat S → ℝ) ((complEquiv2 Γ S T hST).symm ρ).1
              * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv2 Γ S T hST).symm ρ).2)) := rfl
    rw [hS, hT, hbil1, hbil2]
  -- conclusion via ε → 0
  have hfin : ∀ η : stdSimplex ℝ (Γ.CoalStrat ((S ∪ T)ᶜ)),
      Γ.charFun S + Γ.charFun T - 2 * eps
        ≤ Γ.bilin (S ∪ T) (fun τST : Γ.CoalStrat (S ∪ T) => (ξ : Γ.CoalStrat S → ℝ) (toSAgg Γ S T τST) * (ζ : Γ.CoalStrat T → ℝ) (toTAgg Γ S T τST)) (↑η) := by
    intro η
    have e1 : Γ.charFun S - eps < Γ.bilin S (↑ξ) (fun σ : Γ.CoalStrat (Sᶜ) => (ζ : Γ.CoalStrat T → ℝ) ((complEquiv1 Γ S T hST).symm σ).1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv1 Γ S T hST).symm σ).2) :=
      lt_of_lt_of_le hξ (ciInf_le hbdSξ ⟨(fun σ : Γ.CoalStrat (Sᶜ) => (ζ : Γ.CoalStrat T → ℝ) ((complEquiv1 Γ S T hST).symm σ).1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv1 Γ S T hST).symm σ).2), hμ₁mem η⟩)
    have e2 : Γ.charFun T - eps < Γ.bilin T (↑ζ) (fun ρ : Γ.CoalStrat (Tᶜ) => (ξ : Γ.CoalStrat S → ℝ) ((complEquiv2 Γ S T hST).symm ρ).1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv2 Γ S T hST).symm ρ).2) :=
      lt_of_lt_of_le hζ (ciInf_le hbdTζ ⟨(fun ρ : Γ.CoalStrat (Tᶜ) => (ξ : Γ.CoalStrat S → ℝ) ((complEquiv2 Γ S T hST).symm ρ).1 * (η : Γ.CoalStrat ((S ∪ T)ᶜ) → ℝ) ((complEquiv2 Γ S T hST).symm ρ).2), hμ₂mem η⟩)
    rw [master η]
    linarith
  have hlast : Γ.charFun S + Γ.charFun T - 2 * eps ≤ Γ.charFun (S ∪ T) := by
    rw [hcfU]
    refine le_trans (le_ciInf hfin) ?_
    exact le_ciSup hbdUU ⟨(fun τST : Γ.CoalStrat (S ∪ T) => (ξ : Γ.CoalStrat S → ℝ) (toSAgg Γ S T τST) * (ζ : Γ.CoalStrat T → ℝ) (toTAgg Γ S T τST)), hprodmem⟩
  linarith

end PartC

end CFAux

/-- 25.3.1 (von Neumann): the characteristic function `v(S) = Max_ξ Min_η K(ξ, η)` of a
zero-sum game satisfies (25:3:a)–(25:3:c). -/
theorem solution {n : ℕ} (Γ : ZeroSumGame n) : IsCharFunction Γ.charFun :=
  ⟨CFAux.charFun_empty Γ, fun S => CFAux.charFun_compl_neg Γ S,
    fun S T hST => CFAux.charFun_union_ge Γ S T hST⟩
