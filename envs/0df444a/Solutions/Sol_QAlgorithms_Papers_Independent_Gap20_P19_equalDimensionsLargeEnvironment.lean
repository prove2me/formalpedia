-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P19.equalDimensionsLargeEnvironment
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:24:16.891543+00:00
-- url     : https://prove2.me/submissions/f6e82569-ef56-4234-bce3-58052e776d52

import Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_flaggedIdentityDegradable
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap20_P19_symmetricSelfComplement
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P19

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Gap20 QAlgorithms.Papers.Independent.Gap20.P19
open scoped BigOperators Matrix ComplexConjugate ComplexOrder Kronecker
open Filter Topology
open QAlgorithms.Papers.Independent.Information100.P67
open QAlgorithms.Papers.Independent.Claimed50.P48
open QAlgorithms.Papers.Independent.Claimed50.P24 (ChannelEB)
open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)
open QAlgorithms.Papers.Independent.Gap48.P36 (finWeyl WeylLabel)
open QAlgorithms.Papers.Independent.Information100.P69 (choi)
open QAlgorithms.Papers.Independent.Information100.P50 (matrixRange)
open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A B C E F R K A2 B2 E2 : Type}
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]
variable [Fintype C] [DecidableEq C] [Nonempty C]
variable [Fintype E] [DecidableEq E] [Nonempty E]
variable [Fintype F] [DecidableEq F] [Nonempty F]
variable [Fintype R] [DecidableEq R] [Nonempty R]
variable [Fintype K] [DecidableEq K]
variable [Fintype A2] [DecidableEq A2] [Nonempty A2]
variable [Fintype B2] [DecidableEq B2] [Nonempty B2]
variable [Fintype E2] [DecidableEq E2] [Nonempty E2]

theorem S175_fact {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℂ) :
    ∃ (P : Matrix m (Fin M.rank) ℂ) (Q : Matrix (Fin M.rank) n ℂ)
      (L : Matrix (Fin M.rank) m ℂ) (R : Matrix n (Fin M.rank) ℂ),
      M = P * Q ∧ L * P = 1 ∧ Q * R = 1 := by
  set f := M.mulVecLin
  have hr : Module.finrank ℂ (LinearMap.range f) = Module.finrank ℂ (Fin M.rank → ℂ) := by
    rw [Module.finrank_fin_fun]; rfl
  let e := LinearEquiv.ofFinrankEq _ _ hr
  let c : (n → ℂ) →ₗ[ℂ] (Fin M.rank → ℂ) := e.toLinearMap ∘ₗ f.rangeRestrict
  let p : (Fin M.rank → ℂ) →ₗ[ℂ] (m → ℂ) := (LinearMap.range f).subtype ∘ₗ e.symm.toLinearMap
  have hpc : p ∘ₗ c = f := by
    apply LinearMap.ext; intro v; simp [p, c]
  have hc : Function.Surjective c := by
    intro y
    obtain ⟨x, hx⟩ := f.surjective_rangeRestrict (e.symm y)
    exact ⟨x, by simp [c, hx]⟩
  have hp : Function.Injective p := by
    intro a b h
    simpa [p] using h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective p (LinearMap.ker_eq_bot.mpr hp)
  obtain ⟨h, hh⟩ := LinearMap.exists_rightInverse_of_surjective c (LinearMap.range_eq_top.mpr hc)
  refine ⟨LinearMap.toMatrix' p, LinearMap.toMatrix' c, LinearMap.toMatrix' g,
    LinearMap.toMatrix' h, ?_, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', hpc]
    rfl
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', hg, Matrix.toLin'_one]
  · apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', hh, Matrix.toLin'_one]

theorem S175_rank_kron {m n m' n' : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    [Fintype m'] [Fintype n'] [DecidableEq m'] [DecidableEq n']
    (M : Matrix m n ℂ) (N : Matrix m' n' ℂ) : (M ⊗ₖ N).rank = M.rank * N.rank := by
  obtain ⟨P, Q, L, R, hM, hL, hR⟩ := S175_fact M
  obtain ⟨P', Q', L', R', hN, hL', hR'⟩ := S175_fact N
  have hk : M ⊗ₖ N = (P ⊗ₖ P') * (Q ⊗ₖ Q') := by
    rw [← Matrix.mul_kronecker_mul, ← hM, ← hN]
  apply le_antisymm
  · rw [hk]
    refine (Matrix.rank_mul_le_right _ _).trans ?_
    refine (Matrix.rank_le_card_height _).trans ?_
    simp
  · have h1 : (L ⊗ₖ L') * ((M ⊗ₖ N) * (R ⊗ₖ R')) = 1 := by
      rw [hk, Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        ← Matrix.mul_kronecker_mul, hR, hR', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hL, hL']
      simp
    have h2 := Matrix.rank_mul_le_right (L ⊗ₖ L') ((M ⊗ₖ N) * (R ⊗ₖ R'))
    have h3 := Matrix.rank_mul_le_left (M ⊗ₖ N) (R ⊗ₖ R')
    rw [h1, Matrix.rank_one] at h2
    simp at h2
    omega

theorem S175_td {C2 : Type} [Fintype C2] (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ) :
    tensorDilation V W = (V ⊗ₖ W).submatrix (Equiv.prodProdProdComm B B2 C C2) id := by
  ext ⟨⟨b, b2⟩, ⟨c, c2⟩⟩ ⟨a, a2⟩
  rfl

theorem S175_conj {C2 : Type} [Fintype C2] (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ)
    (X : Matrix A A ℂ) (Y : Matrix A2 A2 ℂ) :
    tensorDilation V W * (X ⊗ₖ Y) * (tensorDilation V W)ᴴ =
      ((V * X * Vᴴ) ⊗ₖ (W * Y * Wᴴ)).submatrix (Equiv.prodProdProdComm B B2 C C2)
        (Equiv.prodProdProdComm B B2 C C2) := by
  rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul, ← Matrix.conjTranspose_kronecker,
    S175_td]
  ext i j
  simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]

theorem S175_tr {C2 : Type} [Fintype C2] (M : Matrix (B × C) (B × C) ℂ)
    (N : Matrix (B2 × C2) (B2 × C2) ℂ) :
    traceRight ((M ⊗ₖ N).submatrix (Equiv.prodProdProdComm B B2 C C2)
        (Equiv.prodProdProdComm B B2 C C2)) = traceRight M ⊗ₖ traceRight N := by
  ext ⟨b, b2⟩ ⟨b', b2'⟩
  simp [traceRight, Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem S175_tl {C2 : Type} [Fintype C2] (M : Matrix (B × C) (B × C) ℂ)
    (N : Matrix (B2 × C2) (B2 × C2) ℂ) :
    traceLeft ((M ⊗ₖ N).submatrix (Equiv.prodProdProdComm B B2 C C2)
        (Equiv.prodProdProdComm B B2 C C2)) = traceLeft M ⊗ₖ traceLeft N := by
  ext ⟨b, b2⟩ ⟨b', b2'⟩
  simp [traceLeft, Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem S175_rc {C2 : Type} [Fintype C2] (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ)
    (X : Matrix A A ℂ) (Y : Matrix A2 A2 ℂ) :
    receiverChannel (tensorDilation V W) (X ⊗ₖ Y) = receiverChannel V X ⊗ₖ receiverChannel W Y := by
  unfold receiverChannel; rw [S175_conj, S175_tr]

theorem S175_cc {C2 : Type} [Fintype C2] (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ)
    (X : Matrix A A ℂ) (Y : Matrix A2 A2 ℂ) :
    complementaryChannel (tensorDilation V W) (X ⊗ₖ Y) =
      complementaryChannel V X ⊗ₖ complementaryChannel W Y := by
  unfold complementaryChannel; rw [S175_conj, S175_tl]

theorem S175_ksum {ι κ ι' κ' K1 K2 : Type} [Fintype K1] [Fintype K2]
    (f : K1 → Matrix ι κ ℂ) (g : K2 → Matrix ι' κ' ℂ) :
    (∑ i, f i) ⊗ₖ (∑ j, g j) = ∑ k : K1 × K2, f k.1 ⊗ₖ g k.2 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.sum_apply, Fintype.sum_prod_type, Finset.sum_mul_sum]

theorem S175_kk {K1 K2 ι κ ι' κ' : Type} [Fintype K1] [Fintype K2] [Fintype ι] [Fintype ι']
    (E1 : K1 → Matrix κ ι ℂ) (E2 : K2 → Matrix κ' ι' ℂ) (P : Matrix ι ι ℂ) (Q : Matrix ι' ι' ℂ) :
    krausApply (fun k : K1 × K2 => E1 k.1 ⊗ₖ E2 k.2) (P ⊗ₖ Q) =
      krausApply E1 P ⊗ₖ krausApply E2 Q := by
  unfold krausApply
  rw [S175_ksum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]

theorem S175_linext {ι κ : Type} [Fintype ι] [DecidableEq ι] (F G : Matrix ι ι ℂ → Matrix κ κ ℂ)
    (hF : IsLinearMap ℂ F) (hG : IsLinearMap ℂ G)
    (h : ∀ i j, F (Matrix.single i j 1) = G (Matrix.single i j 1)) : F = G := by
  funext ρ
  have e : ρ = ∑ i, ∑ j, ρ i j • Matrix.single i j (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single ρ]
    simp [Matrix.smul_single]
  let LF := IsLinearMap.mk' F hF
  let LG := IsLinearMap.mk' G hG
  have hF' : F ρ = LF ρ := rfl
  have hG' : G ρ = LG ρ := rfl
  rw [hF', hG', e]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  exact congrArg _ (h i j)

theorem S175_lin_conj {X Y : Type} [Fintype X] [Fintype Y] (U : Matrix Y X ℂ) :
    IsLinearMap ℂ (fun ρ : Matrix X X ℂ => U * ρ * Uᴴ) :=
  ⟨fun a b => by simp [Matrix.mul_add, Matrix.add_mul],
   fun c a => by simp [Matrix.mul_smul, Matrix.smul_mul]⟩

theorem S175_lin_tr {X Y : Type} [Fintype Y] :
    IsLinearMap ℂ (fun ρ : Matrix (X × Y) (X × Y) ℂ => traceRight ρ) :=
  ⟨fun a b => by ext i j; simp [traceRight, Finset.sum_add_distrib],
   fun c a => by ext i j; simp [traceRight, Finset.mul_sum]⟩

theorem S175_lin_tl {X Y : Type} [Fintype X] :
    IsLinearMap ℂ (fun ρ : Matrix (X × Y) (X × Y) ℂ => traceLeft ρ) :=
  ⟨fun a b => by ext i j; simp [traceLeft, Finset.sum_add_distrib],
   fun c a => by ext i j; simp [traceLeft, Finset.mul_sum]⟩

theorem S175_lin_comp {X Y Z : Type} {f : X → Y} {g : Y → Z} [AddCommMonoid X] [AddCommMonoid Y]
    [AddCommMonoid Z] [Module ℂ X] [Module ℂ Y] [Module ℂ Z]
    (hg : IsLinearMap ℂ g) (hf : IsLinearMap ℂ f) : IsLinearMap ℂ (g ∘ f) :=
  ⟨fun a b => by simp [hf.map_add, hg.map_add], fun c a => by simp [hf.map_smul, hg.map_smul]⟩

theorem S175_lin_rc {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] (U : Matrix (Y × Z) X ℂ) :
    IsLinearMap ℂ (receiverChannel U) :=
  S175_lin_comp (f := fun ρ : Matrix X X ℂ => U * ρ * Uᴴ) S175_lin_tr (S175_lin_conj U)

theorem S175_lin_cc {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] (U : Matrix (Y × Z) X ℂ) :
    IsLinearMap ℂ (complementaryChannel U) :=
  S175_lin_comp (f := fun ρ : Matrix X X ℂ => U * ρ * Uᴴ) S175_lin_tl (S175_lin_conj U)

theorem S175_lin_k {K' X Y : Type} [Fintype K'] [Fintype X] (E' : K' → Matrix Y X ℂ) :
    IsLinearMap ℂ (krausApply E') :=
  ⟨fun a b => by simp [krausApply, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib],
   fun c a => by simp [krausApply, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]⟩

theorem S175_chan {K' ι κ : Type} [Fintype K'] [Fintype ι] [Fintype κ] [DecidableEq ι]
    (E : K' → Matrix κ ι ℂ) (h : ∑ j, (E j)ᴴ * E j = 1) : IsChannel (krausApply E) := by
  refine ⟨Fintype.card K', fun j => E ((Fintype.equivFin K').symm j), ?_, fun rho => ?_⟩
  · unfold IsKrausFamily
    rw [← h]; exact Equiv.sum_comp (Fintype.equivFin K').symm (fun j => (E j)ᴴ * E j)
  · unfold krausApply
    exact (Equiv.sum_comp (Fintype.equivFin K').symm (fun j => E j * rho * (E j)ᴴ)).symm

theorem S175_deg (V : Matrix (B × E) A ℂ) (W : Matrix (B2 × E2) A2 ℂ)
    (hV : IsDegradable V) (hW : IsDegradable W) : IsDegradable (tensorDilation V W) := by
  obtain ⟨hVi, D1, ⟨m1, E1, hE1, hD1⟩, hV2⟩ := hV
  obtain ⟨hWi, D2, ⟨m2, E2', hE2, hD2⟩, hW2⟩ := hW
  refine ⟨?_, krausApply (fun k : Fin m1 × Fin m2 => E1 k.1 ⊗ₖ E2' k.2), S175_chan _ ?_, ?_⟩
  · unfold IsIsometry at *
    rw [S175_td]
    have : ((V ⊗ₖ W).submatrix (Equiv.prodProdProdComm B B2 E E2) id)ᴴ *
        (V ⊗ₖ W).submatrix (Equiv.prodProdProdComm B B2 E E2) id = (V ⊗ₖ W)ᴴ * (V ⊗ₖ W) := by
      rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
      simp
    rw [this, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hVi, hWi,
      Matrix.one_kronecker_one]
  · unfold IsKrausFamily at hE1 hE2
    have : ∑ k : Fin m1 × Fin m2, (E1 k.1 ⊗ₖ E2' k.2)ᴴ * (E1 k.1 ⊗ₖ E2' k.2) =
        (∑ i, (E1 i)ᴴ * E1 i) ⊗ₖ (∑ j, (E2' j)ᴴ * E2' j) := by
      rw [S175_ksum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Matrix.conjTranspose_kronecker, Matrix.mul_kronecker_mul]
    rw [this, hE1, hE2, Matrix.one_kronecker_one]
  · intro ρ
    have key := S175_linext (complementaryChannel (tensorDilation V W))
      ((krausApply (fun k : Fin m1 × Fin m2 => E1 k.1 ⊗ₖ E2' k.2)) ∘
        receiverChannel (tensorDilation V W))
      (S175_lin_cc _) (S175_lin_comp (S175_lin_k _) (S175_lin_rc _)) ?_
    · exact congrFun key ρ
    · rintro ⟨a, a2⟩ ⟨c, c2⟩
      have hs : Matrix.single (a, a2) (c, c2) (1 : ℂ) =
          Matrix.single a c (1 : ℂ) ⊗ₖ Matrix.single a2 c2 (1 : ℂ) := by
        rw [Matrix.single_kronecker_single, one_mul]
      simp only [Function.comp_apply]
      rw [hs, S175_cc, S175_rc, S175_kk, hV2, hW2, hD1, hD2]

theorem S175_choi {C2 : Type} [Fintype C2] (V : Matrix (B × C) A ℂ) (W : Matrix (B2 × C2) A2 ℂ) :
    choi (receiverChannel (tensorDilation V W)) =
      (choi (receiverChannel V) ⊗ₖ choi (receiverChannel W)).submatrix
        (Equiv.prodProdProdComm A A2 B B2) (Equiv.prodProdProdComm A A2 B B2) := by
  ext ⟨⟨a, a2⟩, ⟨b, b2⟩⟩ ⟨⟨c, c2⟩, ⟨d, d2⟩⟩
  have hs : Matrix.single (a, a2) (c, c2) (1 : ℂ) =
      Matrix.single a c (1 : ℂ) ⊗ₖ Matrix.single a2 c2 (1 : ℂ) := by
    rw [Matrix.single_kronecker_single, one_mul]
  simp only [choi, Matrix.submatrix_apply, Equiv.prodProdProdComm_apply]
  rw [hs, S175_rc]
  rfl

theorem solution [Nonempty A] [Nonempty E]
    (U : Matrix (A × E) A ℂ) (hU : IsIsometry U)
    (hd : 1 < Fintype.card A) (hfull : (choi (receiverChannel U)).rank = Fintype.card A^2) :
    let V := tensorDilation (flaggedDilation (1/2) U) symmetricIsometry
    IsDegradable V ∧
    Fintype.card (A × Fin 6) = 6*Fintype.card A ∧
    Fintype.card ((Bool × A) × Fin 3) = 6*Fintype.card A ∧
    (choi (receiverChannel V)).rank = 3*(Fintype.card A^2+1) ∧
    6*Fintype.card A < (choi (receiverChannel V)).rank := by
  intro V
  have F := flaggedIdentityDegradable U hU (1/2) (by norm_num) (by norm_num)
  have S := symmetricSelfComplement
  have hid : krausApply (fun _ : Fin 1 => (1 : Matrix (Fin 3) (Fin 3) ℂ)) =
      fun ρ => ρ := by
    funext ρ; simp [krausApply]
  have hSdeg : IsDegradable symmetricIsometry := by
    refine ⟨S.1, fun ρ => ρ, ?_, fun ρ => ?_⟩
    · have := S175_chan (fun _ : Fin 1 => (1 : Matrix (Fin 3) (Fin 3) ℂ)) (by simp)
      rw [hid] at this; exact this
    · rw [S.2.2.1]; rfl
  have hS3 : (choi (receiverChannel symmetricIsometry)).rank = 3 := S.2.2.2.2.2
  have hF : (choi (receiverChannel (flaggedDilation (1/2) U))).rank = 1 + Fintype.card A ^ 2 := by
    rw [F.1, F.2.2.2.2.2.1, hfull]
  have hlt := F.2.2.2.2.2.2 hd hfull
  rw [← F.1] at hlt
  have hrank : (choi (receiverChannel V)).rank = (1 + Fintype.card A ^ 2) * 3 := by
    show (choi (receiverChannel (tensorDilation _ _))).rank = _
    rw [S175_choi, Matrix.rank_submatrix, S175_rank_kron, hF, hS3]
  refine ⟨S175_deg _ _ F.2.2.1 hSdeg, ?_, ?_, ?_, ?_⟩
  · simp [Fintype.card_prod]; ring
  · simp [Fintype.card_prod]; ring
  · rw [hrank]; ring
  · rw [hrank]; rw [hF] at hlt; omega

end
