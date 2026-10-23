-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P14.pathIdempotent_expectation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:42:05.349869+00:00
-- url     : https://prove2.me/submissions/87d0f9ea-60d4-4215-ba2b-a0512be44ac3

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14

open QAlgorithms.Papers.Independent.Support21.P14
open QAlgorithms.Papers.Independent.Next46.P12
open Matrix

noncomputable section

open scoped Classical

namespace X6P14

variable {F : Type*} [Field F]

theorem equiv_central {A : Type*} [Ring A] [Algebra F A] (D : SplitPresentation F A) (l : D.Label) :
    D.equiv (centralIdempotent D l) = Pi.single l 1 := by
  simp [centralIdempotent, blockElement]

theorem equiv_mul_central {A : Type*} [Ring A] [Algebra F A] (D : SplitPresentation F A)
    (l : D.Label) (x : A) :
    D.equiv (x * centralIdempotent D l) = Pi.single l (D.equiv x l) := by
  rw [map_mul, equiv_central]
  funext i
  by_cases h : i = l
  · subst h; simp
  · simp [h]

theorem central_comm {A : Type*} [Ring A] [Algebra F A] (D : SplitPresentation F A)
    (l : D.Label) (x : A) : x * centralIdempotent D l = centralIdempotent D l * x := by
  apply D.equiv.injective
  rw [map_mul, map_mul, equiv_central]
  funext i
  by_cases h : i = l
  · subst h; simp
  · simp [h]

/-- `p` is zero or a rank-one idempotent supported in block `μ`. -/
def RankOneAt {A : Type*} [Ring A] [Algebra F A] (D : SplitPresentation F A) (μ : D.Label)
    (p : A) : Prop :=
  p = 0 ∨ ∃ v φ : Fin (D.size μ) → F, φ ⬝ᵥ v = 1 ∧ D.equiv p = Pi.single μ (vecMulVec v φ)

theorem rank_one_of_finrank {d : ℕ} (Q : Matrix (Fin d) (Fin d) F) (hQ : Q * Q = Q)
    (h : Module.finrank F (LinearMap.range (Matrix.toLin' Q)) ≤ 1) :
    Q = 0 ∨ ∃ w ψ : Fin d → F, ψ ⬝ᵥ w = 1 ∧ Q = vecMulVec w ψ := by
  obtain ⟨g, hg⟩ := finrank_le_one_iff.mp h
  have hc : ∀ j : Fin d, ∃ c : F, c • (g : Fin d → F) = Q *ᵥ Pi.single j 1 := by
    intro j
    obtain ⟨c, hc⟩ := hg ⟨Q *ᵥ Pi.single j 1, LinearMap.mem_range.2 ⟨Pi.single j 1, by simp⟩⟩
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩
  choose ψ hψ using hc
  have hQe : Q = vecMulVec (g : Fin d → F) ψ := by
    ext i j
    have := congrFun (hψ j) i
    simp only [Pi.smul_apply, smul_eq_mul, mulVec_single_one] at this
    rw [vecMulVec_apply]
    simp only [Matrix.col_apply] at this
    rw [← this]; ring
  by_cases hQ0 : Q = 0
  · exact Or.inl hQ0
  · right
    refine ⟨g, ψ, ?_, hQe⟩
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 g.2
    have hQg : Q *ᵥ (g : Fin d → F) = g := by
      rw [← hy, toLin'_apply, mulVec_mulVec, hQ]
    have hg0 : (g : Fin d → F) ≠ 0 := by
      intro h0; apply hQ0; rw [hQe, h0]; ext i j; simp [vecMulVec_apply]
    have hQg2 : vecMulVec (g : Fin d → F) ψ *ᵥ (g : Fin d → F) = g := by rw [← hQe]; exact hQg
    rw [vecMulVec_mulVec] at hQg2
    have : (ψ ⬝ᵥ (g : Fin d → F) - 1) • (g : Fin d → F) = 0 := by
      rw [sub_smul, one_smul]
      have h2 : MulOpposite.op (ψ ⬝ᵥ (g : Fin d → F)) • (g : Fin d → F) =
          (ψ ⬝ᵥ (g : Fin d → F)) • (g : Fin d → F) := by
        funext i; simp [mul_comm]
      rw [← h2, hQg2, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hg0

theorem mul_single {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [∀ i, MulZeroClass (M i)] (f : ∀ i, M i) (i : ι) (y : M i) :
    f * Pi.single i y = Pi.single i (f i * y) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem step {A B : Type*} [Ring A] [Algebra F A] [Ring B] [Algebra F B]
    (DB : SplitPresentation F B) (DA : SplitPresentation F A) (inc : B →ₐ[F] A)
    (hmf : MultiplicityFreeRestriction DB DA inc) (μ : DB.Label) (l : DA.Label) (p : B)
    (hp : RankOneAt DB μ p) : RankOneAt DA l (inc p * centralIdempotent DA l) := by
  rcases hp with rfl | ⟨v, φ, hφv, hpe⟩
  · left; simp
  have hpp : p * p = p := DB.equiv.injective (by
    rw [map_mul, hpe, ← Pi.single_mul, vecMulVec_mul_vecMulVec, hφv, one_smul])
  set Q := DA.equiv (inc p) l with hQdef
  have hQQ : Q * Q = Q := by
    rw [hQdef, ← Pi.mul_apply, ← map_mul, ← map_mul, hpp]
  let s : (Fin (DB.size μ) → F) →ₗ[F] B :=
    { toFun := fun x => DB.equiv.symm (Pi.single μ (vecMulVec x φ))
      map_add' := by
        intro a b
        rw [← map_add, ← Pi.single_add]
        congr 2
        ext i j; simp [vecMulVec_apply, add_mul]
      map_smul' := by
        intro c a
        rw [RingHom.id_apply, ← map_smul, ← Pi.single_smul]
        congr 2
        ext i j; simp [vecMulVec_apply, mul_assoc] }
  have hs : ∀ x, s x = DB.equiv.symm (Pi.single μ (vecMulVec x φ)) := fun x => rfl
  have hsv : s v = p := by rw [hs, ← hpe, AlgEquiv.symm_apply_apply]
  have hsmul : ∀ b x, s (DB.equiv b μ *ᵥ x) = b * s x := by
    intro b x
    apply DB.equiv.injective
    rw [hs, hs, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, mul_single,
      mul_vecMulVec]
  let Ψ : (Fin (DA.size l) → F) →ₗ[F] (SimpleSpace DB μ →ₗ[F] SimpleSpace DA l) :=
    LinearMap.mk₂ F (fun w x => DA.equiv (inc (s x)) l *ᵥ w)
      (fun w1 w2 x => by simp [mulVec_add])
      (fun c w x => by simp [mulVec_smul])
      (fun w x1 x2 => by simp [add_mulVec])
      (fun c w x => by simp [smul_mulVec])
  have hΨ : ∀ w x, Ψ w x = DA.equiv (inc (s x)) l *ᵥ w := fun w x => rfl
  have hmem : ∀ w, Ψ w ∈ restrictionHom DB DA inc μ l := by
    intro w b x
    simp only [simpleAction, toLin'_apply, hΨ]
    rw [hsmul, map_mul, map_mul, Pi.mul_apply, mulVec_mulVec]
  let Φ := (Ψ.codRestrict (restrictionHom DB DA inc μ l) hmem).comp
    (LinearMap.range (Matrix.toLin' Q)).subtype
  have hΦ : Function.Injective Φ := by
    refine (injective_iff_map_eq_zero Φ).2 ?_
    intro w hw
    have h1 := congrArg (fun f : restrictionHom DB DA inc μ l => (f : SimpleSpace DB μ →ₗ[F] SimpleSpace DA l) v) hw
    simp only [Φ, LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply,
      hΨ, hsv] at h1
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 w.2
    have h2 : Q *ᵥ (w : Fin (DA.size l) → F) = w := by
      rw [← hy, toLin'_apply, mulVec_mulVec, hQQ]
    ext1
    rw [← h2]
    simpa [hQdef] using h1
  have hrank : Module.finrank F (LinearMap.range (Matrix.toLin' Q)) ≤ 1 :=
    (LinearMap.finrank_le_finrank_of_injective hΦ).trans (hmf μ l)
  have hEq : DA.equiv (inc p * centralIdempotent DA l) = Pi.single l Q := equiv_mul_central DA l _
  rcases rank_one_of_finrank Q hQQ hrank with h0 | ⟨w, ψ, hψw, hQ⟩
  · left
    apply DA.equiv.injective
    rw [hEq, h0, map_zero, Pi.single_zero]
  · right
    exact ⟨w, ψ, hψw, by rw [hEq, hQ]⟩

variable {A : ℕ → Type*} [∀ k, Ring (A k)] [∀ k, Algebra F (A k)] {n : ℕ}

theorem base_rank (D : FiniteSplitTower F A n) (t : FiniteTowerPath D) :
    RankOneAt (D.split 0 (Nat.zero_le n)) (t.val ⟨0, by omega⟩)
      (finitePathIdempotent D t 0 (Nat.zero_le n)) := by
  set S := D.split 0 (Nat.zero_le n) with hS
  set t0 : S.Label := t.val ⟨0, by omega⟩ with ht0
  have h1 : Module.finrank F (A 0) = 1 := by
    rw [D.base.toLinearEquiv.finrank_eq, Module.finrank_self]
  have h2 : Module.finrank F (A 0) = ∑ i, S.size i * S.size i := by
    rw [S.equiv.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
    simp [Module.finrank_matrix]
  have hsum : ∑ i, S.size i * S.size i = 1 := by rw [← h2, h1]
  have hpos := S.positive
  have huniq : ∀ i, i = t0 := by
    intro i
    by_contra hne
    have := Finset.sum_le_sum_of_subset (f := fun i => S.size i * S.size i)
      (Finset.subset_univ {i, t0})
    rw [Finset.sum_pair hne, hsum] at this
    have := hpos i; have := hpos t0
    nlinarith
  have hsz : S.size t0 = 1 := by
    have := Finset.single_le_sum (f := fun i => S.size i * S.size i) (fun i _ => Nat.zero_le _)
      (Finset.mem_univ t0)
    rw [hsum] at this
    have := hpos t0
    nlinarith
  right
  refine ⟨fun _ => 1, fun _ => 1, ?_, ?_⟩
  · simp [dotProduct]; exact (congrArg (Nat.cast : ℕ → F) hsz).trans Nat.cast_one
  · have hp : finitePathIdempotent D t 0 (Nat.zero_le n) = 1 := by simp [finitePathIdempotent]
    rw [hp, map_one]
    funext i
    obtain rfl := huniq i
    simp only [Pi.single_eq_same, Pi.one_apply]
    ext a b
    have ha : a.val < 1 := lt_of_lt_of_eq a.isLt hsz
    have hb : b.val < 1 := lt_of_lt_of_eq b.isLt hsz
    have hab : a = b := Fin.ext (by omega)
    subst hab
    simp [vecMulVec_apply]

theorem fac (D : FiniteSplitTower F A n) (t : FiniteTowerPath D) (k j : ℕ) (hj : j ≤ n)
    (hkj : k + 1 = j) :
    finitePathIdempotent D t j hj =
      D.inc k j (by omega) hj (finitePathIdempotent D t k (by omega)) *
        centralIdempotent (D.split j hj) (t.val ⟨j, by omega⟩) := by
  subst hkj
  unfold finitePathIdempotent
  rw [List.ofFn_succ', List.prod_concat, map_list_prod, List.map_ofFn]
  congr 1
  · refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    simp only [Function.comp_apply, Fin.val_castSucc]
    rw [← AlgHom.comp_apply, D.comp]
  · show D.inc (k+1) (k+1) _ hj _ = _
    rw [D.self]; rfl

theorem all_rank (D : FiniteSplitTower F A n) (t : FiniteTowerPath D) :
    ∀ k (hk : k ≤ n), RankOneAt (D.split k hk) (t.val ⟨k, by omega⟩)
      (finitePathIdempotent D t k hk)
  | 0, _ => base_rank D t
  | k + 1, hk => by
    rw [fac D t k (k+1) hk rfl]
    exact step _ _ _ (D.multiplicityFree k (by omega)) _ _ _ (all_rank D t k (by omega))

end X6P14

theorem X6P14.single_mul' {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [∀ i, MulZeroClass (M i)] (f : ∀ i, M i) (i : ι) (y : M i) :
    Pi.single i y * f = Pi.single i (y * f i) := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

theorem solution {F : Type*} [Field F] {A : ℕ → Type*}
    [∀ k, Ring (A k)] [∀ k, Algebra F (A k)]
    (n : ℕ) (hn : 1 ≤ n) (D : FiniteSplitTower F A n)
    (epsilon : A n →ₗ[F] F) (htrace : ∀ a b, epsilon (a*b) = epsilon (b*a))
    (E : A n →ₗ[F] A (n-1))
    (hretract : ∀ a, E (D.inc (n-1) n (by omega) le_rfl a) = a)
    (hbimodule : ∀ a b : A (n-1), ∀ x : A n,
      E (D.inc (n-1) n (by omega) le_rfl a * x *
        D.inc (n-1) n (by omega) le_rfl b) = a * E x * b)
    (hpreserve : ∀ x, epsilon (D.inc (n-1) n (by omega) le_rfl (E x)) = epsilon x)
    (hfaithful : ∀ a : A (n-1),
      (∀ b : A (n-1), epsilon (D.inc (n-1) n (by omega) le_rfl (a*b)) = 0) → a = 0)
    (t : FiniteTowerPath D) :
    E (finitePathIdempotent D t n le_rfl) =
      (epsilon (finitePathIdempotent D t n le_rfl) /
        epsilon (D.inc (n-1) n (by omega) le_rfl
          (finitePathIdempotent D t (n-1) (by omega)))) •
        finitePathIdempotent D t (n-1) (by omega) := by
  have hR := X6P14.all_rank D t (n-1) (by omega)
  have hfac : finitePathIdempotent D t n le_rfl =
      D.inc (n-1) n (by omega) le_rfl (finitePathIdempotent D t (n-1) (by omega)) *
        centralIdempotent (D.split n le_rfl) (t.val ⟨n, by omega⟩) :=
    X6P14.fac D t (n-1) n le_rfl (by omega)
  set ι := D.inc (n-1) n (by omega) le_rfl with hι
  set p' := finitePathIdempotent D t (n-1) (by omega) with hp'
  set z := centralIdempotent (D.split n le_rfl) (t.val ⟨n, by omega⟩) with hz
  have hEleft : ∀ a x, E (ι a * x) = a * E x := by
    intro a x; have := hbimodule a 1 x; rwa [map_one, mul_one, mul_one] at this
  have hEright : ∀ b x, E (x * ι b) = E x * b := by
    intro b x; have := hbimodule 1 b x; rwa [map_one, one_mul, one_mul] at this
  have hzc : ∀ y, y * z = z * y := fun y => X6P14.central_comm _ _ y
  have hEz : ∀ a, a * E z = E z * a := by
    intro a; rw [← hEleft, ← hEright, hzc]
  have hEpn : E (ι p' * z) = p' * E z := hEleft p' z
  rw [hfac, hEpn]
  rcases hR with h0 | ⟨v, φ, hφv, hpe⟩
  · rw [h0]; simp
  have hcorner : ∀ b, p' * b * p' =
      (φ ⬝ᵥ ((D.split (n-1) (by omega)).equiv b (t.val ⟨n-1, by omega⟩) *ᵥ v)) • p' := by
    intro b
    apply (D.split (n-1) (by omega)).equiv.injective
    rw [map_mul, map_mul, map_smul, hpe, X6P14.single_mul', ← Pi.single_mul, ← Pi.single_smul,
      mul_assoc, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec]
    congr 1
    ext i j; simp [Matrix.vecMulVec_apply]; ring
  have hidem : p' * p' = p' := by
    have := hcorner 1
    rwa [mul_one, map_one, Pi.one_apply, Matrix.one_mulVec, hφv, one_smul] at this
  set c := φ ⬝ᵥ ((D.split (n-1) (by omega)).equiv (E z) (t.val ⟨n-1, by omega⟩) *ᵥ v) with hc
  have hmain : p' * E z = c • p' := by
    rw [← hcorner, mul_assoc, ← hEz, ← mul_assoc, hidem]
  rw [hmain]
  have htr : epsilon (ι p' * z) = c * epsilon (ι p') := by
    rw [← hpreserve, hEpn, hmain, map_smul, map_smul, smul_eq_mul]
  by_cases hε : epsilon (ι p') = 0
  · have hcp : c • p' = 0 := by
      apply hfaithful
      intro b
      rw [smul_mul_assoc, map_smul, map_smul, smul_eq_mul]
      have h1 : epsilon (ι (p' * b)) = 0 := by
        have e1 : p' * b = p' * (p' * b) := by rw [← mul_assoc, hidem]
        rw [e1, map_mul, htrace, ← map_mul, hcorner, map_smul, map_smul, hε, smul_zero]
      rw [h1, mul_zero]
    rw [hcp, hε, div_zero, zero_smul]
  · rw [htr, mul_div_assoc, div_self hε, mul_one]
