-- Prove2me | solution 1 for TheoryOfGames.GeneralGames.univ_removable_iff
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:03:36.577988+00:00
-- url     : https://prove2.me/submissions/1283d0b9-d09f-45de-b5ec-de33bc754640

import Definitions.Def_TheoryOfGames_GeneralGames_Removable

/-!
# (57:C): `I` is removable iff the game is inessential

For a zero-sum game `Γ`, the whole player set `I` is removable — there is a zero-sum game with
the same restricted characteristic function in which *no* player has any influence — exactly
when `Γ` is inessential, i.e. `v(S) = ∑_{k ∈ S} α_k` for some constants `α`.

* **(←)** Take the constant game `Γ'` with `ℋ'_k ≡ α_k`.  Its restricted characteristic
  function is `∑_{k ∈ S} α_k` at every `S` (a two-person game with constant payoff `c` has
  bilinear form `c` on the simplices), no player has influence, and it is zero-sum because
  `∑_k α_k = v(I) = 0` — the last identity holding in *any* zero-sum game, since the grand
  coalition's payoff is the total payoff `0`.
* **(→)** In a game where no player has influence, every payoff vector `ℋ'(τ)` equals the
  fixed vector `ℋ'(τ*)`: move from an arbitrary profile to `τ*` one coordinate at a time
  (each single-coordinate change preserves `ℋ'` by no-influence at that player).  So `Γ'` is
  effectively constant with `α := ℋ'(τ*)`, and its characteristic function `∑_{k ∈ S} α_k`
  equals `Γ`'s.
-/

open TheoryOfGames.GeneralGames

namespace TGB57C

open GeneralGame

variable {n : ℕ}

/-- Every coalition has an aggregate (all `β k ≥ 1`). -/
private lemma nonempty_coalStrat (Γ : GeneralGame n) (R : Finset (Fin n)) :
    Nonempty (Γ.CoalStrat R) :=
  ⟨fun k => Fin.mk 0 (Γ.β_pos k.1)⟩

/-- The probability simplex on a nonempty type is nonempty (`Pi.single x₀ 1`). -/
private lemma nonempty_simplex {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] :
    Nonempty (stdSimplex ℝ X) :=
  ⟨Pi.single (Classical.arbitrary X) 1,
    single_mem_stdSimplex (𝕜 := ℝ) (Classical.arbitrary X)⟩

/-- Elements of the simplex sum to one. -/
private lemma simplex_sum {X : Type} [Fintype X] [DecidableEq X] (ξ : stdSimplex ℝ X) :
    ∑ i, (ξ : X → ℝ) i = 1 :=
  stdSimplex.sum_eq_one ξ

/-- `Fin.castSucc k` is never the fictitious player, so `extH` reads off `H`. -/
private lemma extH_castSucc (Γ : GeneralGame n) (τ : (k : Fin n) → Fin (Γ.β k)) (k : Fin n) :
    Γ.extH τ (Fin.castSuccEmb k) = Γ.H τ k := by
  simp [GeneralGame.extH]

section ConstantPayoffs

variable (Γ : GeneralGame n) (c : Fin n → ℝ)

/-- With constant payoffs the coalition payoff is `∑_{k ∈ S} c k`, whatever the aggregates. -/
private lemma coalPayoff_const (hconst : ∀ τ, Γ.H τ = c) (S : Finset (Fin n))
    (τS : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb)))
    (τC : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ) :
    Γ.coalPayoff (S.map Fin.castSuccEmb) τS τC = ∑ k ∈ S, c k := by
  unfold coalPayoff
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [extH_castSucc, hconst]

/-- With constant payoffs the bilinear form is `∑_{k ∈ S} c k` for every pair of mixed
strategies. -/
private lemma bilin_const (hconst : ∀ τ, Γ.H τ = c) (S : Finset (Fin n))
    (ξ : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))))
    (η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ)) :
    Γ.bilin (S.map Fin.castSuccEmb) (↑ξ) (↑η) = ∑ k ∈ S, c k := by
  have hcp := coalPayoff_const Γ c hconst S
  have h2 : ∀ τS : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb)),
      (∑ τC : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ,
          (∑ k ∈ S, c k) * (↑ξ : Γ.CoalStrat _ → ℝ) τS * (↑η : Γ.CoalStrat _ → ℝ) τC)
        = (∑ k ∈ S, c k) * (↑ξ : Γ.CoalStrat _ → ℝ) τS
            * (∑ i : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ,
                (↑η : Γ.CoalStrat _ → ℝ) i) := by
    intro τS
    rw [← Finset.mul_sum]
  have h4 : ∀ τS : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb)),
      (∑ k ∈ S, c k) * (↑ξ : Γ.CoalStrat _ → ℝ) τS
          * (∑ i : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ,
              (↑η : Γ.CoalStrat _ → ℝ) i)
        = (∑ k ∈ S, c k)
            * (∑ i : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ,
                (↑η : Γ.CoalStrat _ → ℝ) i)
            * (↑ξ : Γ.CoalStrat _ → ℝ) τS := by
    intro τS
    ring
  have h5 : (∑ k ∈ S, c k)
      * (∑ i : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ,
          (↑η : Γ.CoalStrat _ → ℝ) i)
      * (∑ i : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb)),
          (↑ξ : Γ.CoalStrat _ → ℝ) i)
      = ∑ τS : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb)),
          (∑ k ∈ S, c k)
            * (∑ i : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ,
                (↑η : Γ.CoalStrat _ → ℝ) i)
            * (↑ξ : Γ.CoalStrat _ → ℝ) τS := by
    rw [Finset.mul_sum (s := Finset.univ)
      (f := fun i : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb)) =>
        (↑ξ : Γ.CoalStrat _ → ℝ) i)
      (a := (∑ k ∈ S, c k)
        * (∑ i : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ,
            (↑η : Γ.CoalStrat _ → ℝ) i))]
  calc Γ.bilin (S.map Fin.castSuccEmb) (↑ξ) (↑η)
      = ∑ τS : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb)),
          ∑ τC : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ,
            (∑ k ∈ S, c k) * (↑ξ : Γ.CoalStrat _ → ℝ) τS * (↑η : Γ.CoalStrat _ → ℝ) τC := by
        unfold GeneralGame.bilin
        rw [Finset.sum_congr rfl (fun τS _ =>
          Finset.sum_congr rfl (fun τC _ => by rw [hcp τS τC]))]
    _ = (∑ k ∈ S, c k)
          * (∑ i : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ,
              (↑η : Γ.CoalStrat _ → ℝ) i)
          * (∑ i : Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb)),
              (↑ξ : Γ.CoalStrat _ → ℝ) i) := by
        rw [Finset.sum_congr rfl (fun τS _ => h2 τS)]
        rw [Finset.sum_congr rfl (fun τS _ => h4 τS)]
        exact h5.symm
    _ = ∑ k ∈ S, c k := by
        rw [simplex_sum (X := Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))) ξ,
          simplex_sum (X := Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ) η]
        ring

/-- With constant payoffs the restricted characteristic function is `∑_{k ∈ S} c k`. -/
private lemma restrictedCharFun_const (hconst : ∀ τ, Γ.H τ = c) (S : Finset (Fin n)) :
    Γ.restrictedCharFun S = ∑ k ∈ S, c k := by
  haveI hx : Nonempty (Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))) :=
    nonempty_coalStrat Γ _
  haveI hy : Nonempty (Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ) :=
    nonempty_coalStrat Γ _
  haveI hS : Nonempty (stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart (S.map
      Fin.castSuccEmb)))) :=
    nonempty_simplex
  haveI hC : Nonempty (stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart (S.map
      Fin.castSuccEmb))ᶜ)) :=
    nonempty_simplex
  have inner : ∀ (ξ : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart (S.map
        Fin.castSuccEmb)))),
      (⨅ η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ),
          Γ.bilin (S.map Fin.castSuccEmb) (↑ξ) (↑η)) = ∑ k ∈ S, c k := by
    intro ξ
    have hbc : ∀ (η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart (S.map
          Fin.castSuccEmb))ᶜ)),
        Γ.bilin (S.map Fin.castSuccEmb) (↑ξ) (↑η) = ∑ k ∈ S, c k :=
      fun η => bilin_const Γ c hconst S ξ η
    calc (⨅ η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ),
            Γ.bilin (S.map Fin.castSuccEmb) (↑ξ) (↑η))
        = ⨅ η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ),
              ∑ k ∈ S, c k := congrArg iInf (funext hbc)
      _ = ∑ k ∈ S, c k := by simp
  simp only [restrictedCharFun, extCharFun]
  calc (⨆ ξ : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))),
          ⨅ η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))ᶜ),
            Γ.bilin (S.map Fin.castSuccEmb) (↑ξ) (↑η))
      = ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart (S.map Fin.castSuccEmb))),
            ∑ k ∈ S, c k := congrArg iSup (funext inner)
    _ = ∑ k ∈ S, c k := by simp

end ConstantPayoffs

/-- In a zero-sum game the grand coalition's value is `0`. -/
private lemma restrictedCharFun_univ_zero (Γ : GeneralGame n) (hz : Γ.IsZeroSum) :
    Γ.restrictedCharFun Finset.univ = 0 := by
  haveI hx : Nonempty (Γ.CoalStrat (GeneralGame.realPart (Finset.univ.map
      Fin.castSuccEmb))) :=
    nonempty_coalStrat Γ _
  haveI hy : Nonempty (Γ.CoalStrat (GeneralGame.realPart (Finset.univ.map
      Fin.castSuccEmb))ᶜ) :=
    nonempty_coalStrat Γ _
  haveI hS : Nonempty (stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart
      (Finset.univ.map Fin.castSuccEmb)))) :=
    nonempty_simplex
  haveI hC : Nonempty (stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart
      (Finset.univ.map Fin.castSuccEmb))ᶜ)) :=
    nonempty_simplex
  have hcp : ∀ (τS : Γ.CoalStrat (GeneralGame.realPart (Finset.univ.map Fin.castSuccEmb)))
        (τC : Γ.CoalStrat (GeneralGame.realPart (Finset.univ.map Fin.castSuccEmb))ᶜ),
      Γ.coalPayoff (Finset.univ.map Fin.castSuccEmb) τS τC = 0 := by
    intro τS τC
    unfold coalPayoff
    rw [Finset.sum_map]
    have hsum := hz (Γ.joint (GeneralGame.realPart (Finset.univ.map Fin.castSuccEmb)) τS τC)
    refine (Finset.sum_congr rfl (fun k _ => ?_)).trans hsum
    rw [extH_castSucc]
  have inner : ∀ (ξ : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart
        (Finset.univ.map Fin.castSuccEmb)))),
      (⨅ η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart
            (Finset.univ.map Fin.castSuccEmb))ᶜ),
          Γ.bilin (Finset.univ.map Fin.castSuccEmb) (↑ξ) (↑η)) = 0 := by
    intro ξ
    have hbc : ∀ (η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart
          (Finset.univ.map Fin.castSuccEmb))ᶜ)),
        Γ.bilin (Finset.univ.map Fin.castSuccEmb) (↑ξ) (↑η) = 0 := by
      intro η
      unfold GeneralGame.bilin
      rw [Finset.sum_congr rfl (fun τS _ =>
        Finset.sum_congr rfl (fun τC _ => by rw [hcp τS τC]))]
      simp
    calc (⨅ η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart
              (Finset.univ.map Fin.castSuccEmb))ᶜ),
            Γ.bilin (Finset.univ.map Fin.castSuccEmb) (↑ξ) (↑η))
        = ⨅ η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart
              (Finset.univ.map Fin.castSuccEmb))ᶜ), (0 : ℝ) := congrArg iInf (funext hbc)
      _ = 0 := by simp
  simp only [restrictedCharFun, extCharFun]
  calc (⨆ ξ : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart
            (Finset.univ.map Fin.castSuccEmb))),
          ⨅ η : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart
              (Finset.univ.map Fin.castSuccEmb))ᶜ),
            Γ.bilin (Finset.univ.map Fin.castSuccEmb) (↑ξ) (↑η))
      = ⨆ ξ : stdSimplex ℝ (Γ.CoalStrat (GeneralGame.realPart
            (Finset.univ.map Fin.castSuccEmb))), (0 : ℝ) := congrArg iSup (funext inner)
    _ = 0 := by simp

end TGB57C

open TheoryOfGames.GeneralGames GeneralGame

/-- The constant game with payoffs `c`. -/
private def constGame {n : ℕ} (c : Fin n → ℝ) : GeneralGame n where
  β := fun _ => 1
  β_pos := fun _ => by norm_num
  H := fun _ => c

open TGB57C

theorem solution {n : ℕ} (Γ : GeneralGame n) (hΓ : Γ.IsZeroSum) :
    Γ.IsRemovable Finset.univ ↔ IsInessential Γ.restrictedCharFun := by
  constructor
  · -- removable → inessential
    rintro ⟨Γ', hz', hv', hnoinf⟩
    have τstar : (k : Fin n) → Fin (Γ'.β k) := fun k => Fin.mk 0 (Γ'.β_pos k)
    -- every payoff vector of Γ' equals the fixed one
    have hconst : ∀ τ : (k : Fin n) → Fin (Γ'.β k), Γ'.H τ = Γ'.H τstar := by
      intro τ
      have key : ∀ m : ℕ, Γ'.H (fun (i : Fin n) => if (i : ℕ) < m then τstar i else τ i) = Γ'.H τ := by
        intro m
        induction m with
        | zero => congr 1
        | succ m ih =>
          rcases Nat.lt_or_ge m n with hm | hm
          · -- one more coordinate gets fixed
            have hstep : Γ'.H (fun (i : Fin n) => if (i : ℕ) < m + 1 then τstar i else τ i)
                = Γ'.H (fun (i : Fin n) => if (i : ℕ) < m then τstar i else τ i) := by
              refine hnoinf ⟨m, hm⟩ (Finset.mem_univ _)
                (fun (i : Fin n) => if (i : ℕ) < m + 1 then τstar i else τ i)
                (fun (i : Fin n) => if (i : ℕ) < m then τstar i else τ i)
                (fun i hi => ?_)
              rcases lt_trichotomy (i : ℕ) m with h1 | h1 | h1
              · rw [if_pos (Nat.lt_succ_of_lt h1), if_pos h1]
              · exact absurd (Fin.ext h1) hi
              · rw [if_neg (show ¬((i : ℕ) < m + 1) by omega),
                  if_neg (show ¬((i : ℕ) < m) by omega)]
            rw [hstep, ih]
          · -- beyond the last player the profiles no longer change
            have hfun : (fun (i : Fin n) => if (i : ℕ) < m + 1 then τstar i else τ i)
                = fun (i : Fin n) => if (i : ℕ) < m then τstar i else τ i := by
              funext i
              have him : (i : ℕ) < m := Nat.lt_of_lt_of_le (Fin.isLt i) hm
              rw [if_pos (Nat.lt_succ_of_lt him), if_pos him]
            rw [hfun]
            exact ih
      have hfun : (fun (i : Fin n) => if (i : ℕ) < n then τstar i else τ i) = τstar := by
        funext i
        simp [Nat.lt_succ_of_lt (Fin.isLt i)]
      have h0 : τ = (fun (i : Fin n) => if (i : ℕ) < 0 then τstar i else τ i) := by
        funext i
        simp
      calc Γ'.H τ = Γ'.H (fun (i : Fin n) => if (i : ℕ) < 0 then τstar i else τ i) :=
            congrArg Γ'.H h0
        _ = Γ'.H τstar := (key 0).trans ((key n).symm.trans (congrArg Γ'.H hfun))
    refine ⟨Γ'.H τstar, fun S => ?_⟩
    have h1 := restrictedCharFun_const Γ' (Γ'.H τstar) hconst S
    rw [← hv']
    exact h1
  · -- inessential → removable
    rintro ⟨α, hα⟩
    have huniv : ∑ k, α k = 0 := by
      have h1 : (0 : ℝ) = ∑ k, α k := by
        have h2 := hα Finset.univ
        rw [restrictedCharFun_univ_zero Γ hΓ] at h2
        simpa using h2
      exact h1.symm
    refine ⟨constGame α, ?_, ?_, ?_⟩
    · intro τ
      simpa [constGame] using huniv
    · funext S
      rw [restrictedCharFun_const (constGame α) α (fun _ => rfl) S]
      exact (hα S).symm
    · intro j _ τ τ' _
      rfl
