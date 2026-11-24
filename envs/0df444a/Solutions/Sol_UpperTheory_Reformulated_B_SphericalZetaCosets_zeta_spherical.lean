-- Prove2me | solution 1 for UpperTheory.Reformulated.B.SphericalZetaCosets.zeta_spherical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:31:18.501263+00:00
-- url     : https://prove2.me/submissions/d04d18e0-fe34-45da-a997-9c62c2c5b9d9

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SphericalZetaCosets
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


section
open MeasureTheory Matrix
open scoped ValuativeRel
namespace UpperTheory.Reformulated.B.SphericalZetaCosets
section Sums
private theorem sum_sigma_geom (T : ℕ → Type) [∀ n, Finite (T n)] (N : ℕ)
    (hT : ∀ n, Nat.card (T n) = N ^ n) (y : ℂ) (hy : ‖(N : ℂ) * y‖ < 1) :
    Summable (fun x : Σ n, T n => ‖y ^ x.1‖) ∧
      ∑' x : Σ n, T n, y ^ x.1 = (1 - (N : ℂ) * y)⁻¹ := by
  have hs : Summable (fun x : Σ n, T n => ‖y ^ x.1‖) := by
    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    refine ⟨fun n => Summable.of_finite, ?_⟩
    refine (summable_geometric_of_lt_one (norm_nonneg _) hy).congr fun n => ?_
    simp [tsum_const, hT, mul_pow]
  refine ⟨hs, ?_⟩
  rw [hs.of_norm.tsum_sigma, ← tsum_geometric_of_norm_lt_one hy]
  refine tsum_congr fun n => ?_
  simp [tsum_const, hT, mul_pow]
private theorem sum_pi_prod : ∀ (c : ℕ) (T : Fin c → Type) (f : ∀ i, T i → ℂ),
    (∀ i, Summable fun x => ‖f i x‖) →
    Summable (fun p : ∀ i, T i => ‖∏ i, f i (p i)‖) ∧
      ∑' p : ∀ i, T i, ∏ i, f i (p i) = ∏ i, ∑' x, f i x := by
  intro c
  induction c with
  | zero =>
    intro T f _
    exact ⟨Summable.of_finite, by simp⟩
  | succ c ih =>
    intro T f hf
    obtain ⟨h1, h2⟩ := ih (fun i => T i.succ) (fun i => f i.succ) (fun i => hf i.succ)
    constructor
    · rw [← (Fin.consEquiv T).summable_iff]
      refine (Summable.mul_norm (hf 0) h1).congr fun x => ?_
      simp [Fin.prod_univ_succ, Fin.consEquiv]
    · rw [← (Fin.consEquiv T).tsum_eq, Fin.prod_univ_succ, ← h2,
        tsum_mul_tsum_of_summable_norm (hf 0) h1]
      refine tsum_congr fun x => ?_
      simp [Fin.prod_univ_succ, Fin.consEquiv]
end Sums
section Hermite
variable {R : Type} [CommRing R] {c : ℕ}
private theorem hnf_diag (π : R) (p : ∀ i : Fin c, Row π i) (i : Fin c) :
    hnf π p i i = π ^ (p i).1 := by simp [hnf, rowFn]
private theorem hnf_low (π : R) (p : ∀ i : Fin c, Row π i) {i j : Fin c} (h : j < i) :
    hnf π p i j = 0 := by simp [hnf, rowFn, h.not_gt, h.ne]
private theorem hnf_up (π : R) (p : ∀ i : Fin c, Row π i) {i j : Fin c} (h : i < j) :
    hnf π p i j = ((p i).2 ⟨j, h⟩).out := by simp [hnf, rowFn, h]
private theorem tri_mulVec [IsDomain R] (H : Matrix (Fin c) (Fin c) R)
    (hl : ∀ i j, j < i → H i j = 0) (hd : ∀ i, H i i ≠ 0) (x : Fin c → R) (i : Fin c)
    (hx : ∀ l, i < l → (H *ᵥ x) l = 0) : (H *ᵥ x) i = H i i * x i := by
  have key : ∀ l, (∀ m, l < m → x m = 0) → (H *ᵥ x) l = H l l * x l := by
    intro l hm
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_single l (fun m _ hne => ?_) (by simp)
    rcases lt_or_gt_of_ne hne with h | h
    · simp [hl l m h]
    · simp [hm m h]
  have z : ∀ l, i < l → x l = 0 := by
    intro l
    induction l using WellFoundedGT.induction with
    | ind l ih =>
      intro hil
      have := key l fun m hm => ih m hm (hil.trans hm)
      rw [hx l hil] at this
      exact (mul_eq_zero.1 this.symm).resolve_left (hd l)
  exact key i z
private theorem hnf_unique [IsDomain R] {π : R} (hπ : Irreducible π)
    (p p' : ∀ i : Fin c, Row π i) (k k' : Matrix (Fin c) (Fin c) R)
    (h : hnf π p' = hnf π p * k) (h' : hnf π p = hnf π p' * k') : p = p' := by
  have hd : ∀ (p : ∀ i : Fin c, Row π i) i, hnf π p i i ≠ 0 := fun p i => by
    rw [hnf_diag]; exact pow_ne_zero _ hπ.ne_zero
  have hle : ∀ (p p' : ∀ i : Fin c, Row π i) (k : Matrix (Fin c) (Fin c) R),
      hnf π p' = hnf π p * k → ∀ i, (p i).1 ≤ (p' i).1 := by
    intro p p' k h i
    have e : ∀ l, (hnf π p *ᵥ fun m => k m i) l = hnf π p' l i := fun l => by
      rw [h]; rfl
    have := tri_mulVec (hnf π p) (fun _ _ => hnf_low π p) (hd p) (fun m => k m i) i
      (fun l hl => by rw [e, hnf_low π p' hl])
    rw [e, hnf_diag, hnf_diag] at this
    exact (pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit).1 ⟨_, this⟩
  have ha : ∀ i, (p i).1 = (p' i).1 := fun i => le_antisymm (hle p p' k h i) (hle p' p k' h' i)
  have row : ∀ (i : Fin c) (x y : Row π i), x.1 = y.1 → ∀ j, π ^ x.1 ∣ (y.2 j).out - (x.2 j).out →
      (y.2 j).out = (x.2 j).out := by
    rintro i ⟨n, r⟩ ⟨m, s⟩ rfl j hj
    have : Ideal.Quotient.mk (Ideal.span {π ^ n}) (s j).out =
        Ideal.Quotient.mk (Ideal.span {π ^ n}) (r j).out :=
      Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hj)
    rw [Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at this
    simp [this]
  have row' : ∀ (i : Fin c) (x y : Row π i), x.1 = y.1 → (∀ j, (y.2 j).out = (x.2 j).out) → x = y := by
    rintro i ⟨n, r⟩ ⟨m, s⟩ rfl hj
    congr 1
    funext j
    exact (Quotient.out_injective (hj j)).symm
  have ent : ∀ j l, hnf π p' l j = hnf π p l j := by
    intro j l
    have e : ∀ l, (hnf π p *ᵥ fun m => (k - 1) m j) l = hnf π p' l j - hnf π p l j := fun l => by
      have : hnf π p * (k - 1) = hnf π p' - hnf π p := by rw [mul_sub, ← h, mul_one]
      rw [← Matrix.sub_apply, ← this]; rfl
    induction l using WellFoundedGT.induction with
    | ind l ih =>
      rcases lt_trichotomy l j with hlj | rfl | hlj
      · have := tri_mulVec (hnf π p) (fun _ _ => hnf_low π p) (hd p) (fun m => (k - 1) m j) l
          (fun m hm => by rw [e, ih m hm, sub_self])
        rw [e, hnf_diag, hnf_up π p hlj, hnf_up π p' hlj] at this
        rw [hnf_up π p hlj, hnf_up π p' hlj]
        exact row l _ _ (ha l) _ ⟨_, this⟩
      · rw [hnf_diag, hnf_diag, ha]
      · rw [hnf_low π p hlj, hnf_low π p' hlj]
  funext i
  refine row' i _ _ (ha i) fun j => ?_
  rw [← hnf_up π p j.2, ← hnf_up π p' j.2, ent]
private theorem hnf_exists [IsDomain R] [IsDiscreteValuationRing R] {π : R} (hπ : Irreducible π)
    (G : Matrix (Fin c) (Fin c) R) (hG : G.det ≠ 0) :
    ∃ (p : ∀ i : Fin c, Row π i) (k k' : Matrix (Fin c) (Fin c) R),
      hnf π p = G * k ∧ G = hnf π p * k' := by
  classical
  set N : Submodule R (Fin c → R) := LinearMap.range G.mulVecLin with hN
  have step : ∀ i : Fin c, ∃ (n : ℕ) (v : Fin c → R), v ∈ N ∧ (∀ l, i < l → v l = 0) ∧
      v i = π ^ n ∧ ∀ w ∈ N, (∀ l, i < l → w l = 0) → π ^ n ∣ w i := by
    intro i
    let M : Submodule R (Fin c → R) := N ⊓ Submodule.pi {l | i < l} fun _ => (⊥ : Submodule R R)
    have hM : ∀ w, w ∈ M ↔ w ∈ N ∧ ∀ l, i < l → w l = 0 := fun w => by
      exact Submodule.mem_inf.trans (and_congr_right fun _ => Submodule.mem_pi)
    let I : Ideal R := M.map (LinearMap.proj i)
    have hI : I ≠ ⊥ := by
      refine (Submodule.ne_bot_iff _).2 ⟨G.det, ⟨Pi.single i G.det, (hM _).2 ⟨?_, ?_⟩, by simp⟩, hG⟩
      · refine ⟨G.adjugate *ᵥ Pi.single i 1, ?_⟩
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_adjugate]
        funext l
        by_cases h : l = i <;> simp [h, Matrix.smul_mulVec]
      · intro l hl
        simp [hl.ne']
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hπ
    obtain ⟨v, hv, hv'⟩ : π ^ n ∈ I := hn ▸ Ideal.mem_span_singleton_self _
    refine ⟨n, v, ((hM v).1 hv).1, ((hM v).1 hv).2, hv', fun w hw hw' => ?_⟩
    rw [← Ideal.mem_span_singleton, ← hn]
    exact ⟨w, (hM w).2 ⟨hw, hw'⟩, rfl⟩
  choose a v hvN hv0 hvd hdv using step
  have red : ∀ m : ℕ, ∀ w ∈ N, ∃ u ∈ N, (∀ l : Fin c, m ≤ l.val → u l = w l) ∧
      ∀ l : Fin c, l.val < m → u l = (Ideal.Quotient.mk (Ideal.span {π ^ a l}) (u l)).out := by
    intro m
    induction m with
    | zero => exact fun w hw => ⟨w, hw, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro w hw
      by_cases hm : m < c
      · let i : Fin c := ⟨m, hm⟩
        obtain ⟨t, ht⟩ : π ^ a i ∣ w i - (Ideal.Quotient.mk (Ideal.span {π ^ a i}) (w i)).out := by
          rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
        obtain ⟨u, hu, h1, h2⟩ := ih (w - t • v i) (N.sub_mem hw (N.smul_mem t (hvN i)))
        refine ⟨u, hu, fun l hl => ?_, fun l hl => ?_⟩
        · rw [h1 l (by omega)]
          simp [hv0 i l (show m < l.val by omega)]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | h
          · exact h2 l h
          · obtain rfl : l = i := Fin.ext h
            have : u i = (Ideal.Quotient.mk (Ideal.span {π ^ a i}) (w i)).out := by
              rw [h1 i le_rfl]
              simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hvd]
              linear_combination ht
            rw [this, Ideal.Quotient.mk_out]
      · obtain ⟨u, hu, h1, h2⟩ := ih w hw
        exact ⟨u, hu, fun l hl => h1 l (by omega), fun l _ => h2 l (by omega)⟩
  choose u huN hu1 hu2 using fun j : Fin c => red j.val (v j) (hvN j)
  let p : ∀ i : Fin c, Row π i := fun i => ⟨a i, fun j => Ideal.Quotient.mk _ (u j i)⟩
  have hp : ∀ i j, hnf π p i j = u j i := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hnf_up π p h]; exact (hu2 j i h).symm
    · rw [hnf_diag, hu1 i i le_rfl, hvd]
    · rw [hnf_low π p h, hu1 j i h.le, hv0 j i h]
  have span : ∀ m : ℕ, ∀ w ∈ N, (∀ l : Fin c, m ≤ l.val → w l = 0) →
      ∃ x, w = hnf π p *ᵥ x := by
    intro m
    induction m with
    | zero => exact fun w _ h => ⟨0, by funext l; simp [h l (Nat.zero_le _)]⟩
    | succ m ih =>
      intro w hw h0
      by_cases hm : m < c
      · let i : Fin c := ⟨m, hm⟩
        obtain ⟨t, ht⟩ := hdv i w hw fun l hl => h0 l hl
        obtain ⟨x, hx⟩ := ih (w - t • u i) (N.sub_mem hw (N.smul_mem t (huN i))) (by
          intro l hl
          rcases hl.eq_or_lt with h | h
          · obtain rfl : l = i := Fin.ext h.symm
            simp [hu1 i i le_rfl, hvd, ht, mul_comm]
          · simp [h0 l h, hu1 i l hl, hv0 i l h])
        refine ⟨x + Pi.single i t, ?_⟩
        rw [Matrix.mulVec_add, ← hx]
        funext l
        simp [hp, mul_comm]
      · exact ih w hw fun l hl => absurd l.2 (by omega)
  choose x hx using huN
  choose y hy using fun j : Fin c => span c (G *ᵥ Pi.single j 1) ⟨Pi.single j 1, rfl⟩
    fun l hl => absurd l.2 (by omega)
  refine ⟨p, Matrix.of fun i j => x j i, Matrix.of fun i j => y j i, ?_, ?_⟩
  · ext i j
    rw [hp, ← hx j]; rfl
  · ext i j
    have := congrFun (hy j) i
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
    rw [this]; rfl
end Hermite
private theorem integral_cosets {G ι : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    [Countable ι] (K : Subgroup G) (hK : MeasurableSet (K : Set G)) (κ : Measure G)
    [κ.IsMulLeftInvariant] (h1 : κ K = 1) (g : ι → G)
    (hg : ∀ i j, (g i)⁻¹ * g j ∈ K → i = j) (f : G → ℂ) (v : ι → ℂ)
    (hf : ∀ i, ∀ k ∈ K, f (g i * k) = v i) (hv : Summable fun i => ‖v i‖) (S : Set G)
    (hS : ∀ x, x ∈ S ↔ ∃ i, (g i)⁻¹ * x ∈ K) :
    IntegrableOn f S κ ∧ ∫ x in S, f x ∂κ = ∑' i, v i := by
  let C : ι → Set G := fun i => (fun x => (g i)⁻¹ * x) ⁻¹' K
  have hSC : S = ⋃ i, C i := by
    ext x; rw [hS, Set.mem_iUnion]; rfl
  have hm : ∀ i, MeasurableSet (C i) := fun i => measurable_const_mul _ hK
  have hκ : ∀ i, κ (C i) = 1 := fun i => (measure_preimage_mul κ _ _).trans h1
  have he : ∀ i, Set.EqOn f (fun _ => v i) (C i) := fun i x hx => by
    have := hf i _ hx
    rwa [mul_inv_cancel_left] at this
  have hd : Pairwise (Function.onFun Disjoint C) := fun i j hij => by
    refine Set.disjoint_left.2 fun x hi hj => hij (hg i j ?_)
    have := K.mul_mem hi (K.inv_mem hj)
    simpa [mul_assoc] using this
  have hi : ∀ i, IntegrableOn f (C i) κ := fun i =>
    (integrableOn_congr_fun (he i) (hm i)).2 (integrableOn_const (by simp [hκ]))
  have hn : ∀ i, ∫ x in C i, ‖f x‖ ∂κ = ‖v i‖ := fun i => by
    rw [setIntegral_congr_fun (g := fun _ => ‖v i‖) (hm i) fun x hx => by simp [he i hx]]
    simp [Measure.real, hκ]
  have hI : IntegrableOn f (⋃ i, C i) κ :=
    integrableOn_iUnion_of_summable_integral_norm hi (by simpa only [hn] using hv)
  rw [hSC]
  refine ⟨hI, ?_⟩
  rw [integral_iUnion hm hd hI]
  refine tsum_congr fun i => ?_
  rw [setIntegral_congr_fun (hm i) (he i)]
  simp [Measure.real, hκ]
private theorem card_quot_pow {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {π : R} (hπ : Irreducible π) (n : ℕ) :
    Nat.card (R ⧸ Ideal.span {π ^ n}) = Nat.card (IsLocalRing.ResidueField R) ^ n := by
  have h := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).1 hπ
  rw [← Ideal.span_singleton_pow, ← h]
  exact cardQuot_pow_of_prime (IsDiscreteValuationRing.not_a_field R)
private theorem isInt_iff {F : Type} [Field F] (O : Subring F) {c : ℕ}
    (Z : Matrix (Fin c) (Fin c) F) :
    GlobalTheory.CompanionTheory.QL.IsInt O Z ↔ ∃ Y : Matrix (Fin c) (Fin c) O, O.subtype.mapMatrix Y = Z := by
  constructor
  · exact fun h => ⟨Matrix.of fun a b => ⟨Z a b, h a b⟩, rfl⟩
  · rintro ⟨Y, rfl⟩ a b
    exact (Y a b).2
private theorem isOpen_GLint {F : Type} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (O : Subring F) (hO : IsOpen (O : Set F)) (c : ℕ) :
    IsOpen (GlobalTheory.CompanionTheory.QL.GLint O c : Set (GL (Fin c) F)) := by
  have h : IsOpen {Z : Matrix (Fin c) (Fin c) F | GlobalTheory.CompanionTheory.QL.IsInt O Z} := by
    simp only [GlobalTheory.CompanionTheory.QL.IsInt, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
      hO.preimage (continuous_apply_apply a b)
  exact (h.preimage Units.continuous_val).inter (h.preimage Units.continuous_coe_inv)
end UpperTheory.Reformulated.B.SphericalZetaCosets
end

set_option autoImplicit false
open MeasureTheory Matrix
open scoped ValuativeRel
open UpperTheory.Reformulated.B.SphericalZetaCosets
namespace UpperTheory.Reformulated.B.SphericalZetaCosets
theorem _root_.solution :
    ∀ {F : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F]
      [inst_3 : IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ},
      GlobalTheory.CompanionTheory.QL.LF O ϖ nrm q →
        ∀ {c : ℕ} (χ : Fin c → F → ℂ) (α : Fin c → ℂ),
          GlobalTheory.CompanionTheory.QL.UnrChar nrm q χ α →
            ∀ (φ : GL (Fin c) F → ℂ),
              GlobalTheory.CompanionTheory.QL.IsSphFn O nrm χ φ →
                ∀ (κ : MeasureTheory.Measure (GL (Fin c) F)),
                  κ.IsMulLeftInvariant →
                    (κ : Set (GL (Fin c) F) → ENNReal) (↑(GlobalTheory.CompanionTheory.QL.GLint O c) : Set (GL (Fin c) F)) = (1 : ENNReal) →
                      ∀ (σ : ℝ),
                        (∀ (i : Fin c), ‖α i‖ * (↑q : ℝ) ^ (((↑c : ℝ) - (1 : ℝ)) / (2 : ℝ) - σ) < (1 : ℝ)) →
                          MeasureTheory.IntegrableOn
                              (fun (g : GL (Fin c) F) ↦
                                φ g * (↑((nrm : F → ℝ) (↑g : Matrix (Fin c) (Fin c) F).det ^ σ) : ℂ))
                              (GlobalTheory.CompanionTheory.QL.Mint O c) κ ∧
                            ∫ (g : GL (Fin c) F) in GlobalTheory.CompanionTheory.QL.Mint O c,
                                φ g * (↑((nrm : F → ℝ) (↑g : Matrix (Fin c) (Fin c) F).det ^ σ) : ℂ) ∂κ =
                              ∏ i : Fin c, ((1 : ℂ) - α i * (↑((↑q : ℝ) ^ (((↑c : ℝ) - (1 : ℝ)) / (2 : ℝ) - σ)) : ℂ))⁻¹ := by
  intro F _ _ _ _ O ϖ nrm q hLF c χ α hχ φ hφ κ hκ h1 σ hσ
  obtain ⟨rfl, hne, hlt, hq, hunit, hpi⟩ := hLF
  have hϖ : ValuativeRel.valuation F ϖ < 1 := (hlt ϖ).2 ⟨1, one_mem _, (mul_one _).symm⟩
  let π : 𝒪[F] := ⟨ϖ, hϖ.le⟩
  have hπ : Irreducible π := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    ext x
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one,
      hlt, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨o, ho, h⟩
      exact ⟨⟨o, ho⟩, Subtype.ext h⟩
    · rintro ⟨o, h⟩
      exact ⟨o, o.2, congrArg Subtype.val h⟩
  have hq0 : 0 < q := by rw [hq]; exact Nat.card_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hcard : ∀ n : ℕ, Nat.card (𝒪[F] ⧸ Ideal.span {π ^ n}) = q ^ n := fun n => by
    rw [hq]; exact card_quot_pow hπ n
  haveI hfin : ∀ n : ℕ, Finite (𝒪[F] ⧸ Ideal.span {π ^ n}) := fun n =>
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  let ι : Matrix (Fin c) (Fin c) 𝒪[F] →+* Matrix (Fin c) (Fin c) F := (𝒪[F]).subtype.mapMatrix
  have hι : Function.Injective ι := fun A B h => by
    ext i j
    exact congrFun (congrFun h i) j
  have htri : ∀ p : ∀ i : Fin c, Row π i, (ι (hnf π p)).BlockTriangular id := fun p i j h => by
    change ((hnf π p i j : 𝒪[F]) : F) = 0
    rw [hnf_low π p (show j < i from h)]; rfl
  have hdiag : ∀ (p : ∀ i : Fin c, Row π i) i, ι (hnf π p) i i = ϖ ^ (p i).1 := fun p i => by
    change ((hnf π p i i : 𝒪[F]) : F) = _
    rw [hnf_diag]; rfl
  have hdet : ∀ p : ∀ i : Fin c, Row π i, (ι (hnf π p)).det = ∏ i, ϖ ^ (p i).1 := fun p => by
    rw [Matrix.det_of_upperTriangular (htri p)]
    exact Finset.prod_congr rfl fun i _ => hdiag p i
  let g : (∀ i : Fin c, Row π i) → GL (Fin c) F := fun p =>
    Matrix.GeneralLinearGroup.mkOfDetNeZero (ι (hnf π p))
      (by rw [hdet]; exact Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ hne)
  have hg : ∀ p, (g p : Matrix (Fin c) (Fin c) F) = ι (hnf π p) := fun p => rfl
  have hK : ∀ x y : GL (Fin c) F, x⁻¹ * y ∈ GlobalTheory.CompanionTheory.QL.GLint 𝒪[F] c ↔
      ∃ k k', (y : Matrix (Fin c) (Fin c) F) = x * ι k ∧
        (x : Matrix (Fin c) (Fin c) F) = y * ι k' := by
    intro x y
    change GlobalTheory.CompanionTheory.QL.IsInt _ _ ∧ GlobalTheory.CompanionTheory.QL.IsInt _ _ ↔ _
    rw [isInt_iff, isInt_iff, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul]
    constructor
    · rintro ⟨⟨k, hk⟩, k', hk'⟩
      exact ⟨k, k', ((Units.eq_inv_mul_iff_mul_eq _).1 hk).symm,
        ((Units.eq_inv_mul_iff_mul_eq _).1 hk').symm⟩
    · rintro ⟨k, k', hk, hk'⟩
      exact ⟨⟨k, (Units.eq_inv_mul_iff_mul_eq _).2 hk.symm⟩, k',
        (Units.eq_inv_mul_iff_mul_eq _).2 hk'.symm⟩
  have hdetK : ∀ k ∈ GlobalTheory.CompanionTheory.QL.GLint 𝒪[F] c, nrm (k : Matrix (Fin c) (Fin c) F).det = 1 := by
    rintro k ⟨hk, hk'⟩
    obtain ⟨A, hA⟩ := (isInt_iff _ _).1 hk
    obtain ⟨B, hB⟩ := (isInt_iff _ _).1 hk'
    have hAB : A * B = 1 := hι (by
      rw [map_mul, map_one]; change (𝒪[F]).subtype.mapMatrix A * (𝒪[F]).subtype.mapMatrix B = 1
      rw [hA, hB, Units.mul_inv])
    apply hunit
    rw [← hA, ← RingHom.map_det]
    exact (Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.integer.integers _)).1
      (Matrix.isUnit_det_of_right_inverse hAB)
  let y : Fin c → ℂ := fun i => α i * (((q : ℝ) ^ ((i : ℕ) - ((c : ℝ) - 1) / 2 - σ) : ℝ) : ℂ)
  have hy : ∀ i : Fin c, ((q ^ (c - 1 - i) : ℕ) : ℂ) * y i =
      α i * (((q : ℝ) ^ (((c : ℝ) - 1) / 2 - σ) : ℝ) : ℂ) := by
    intro i
    have e : ((c - 1 - i : ℕ) : ℝ) = (c : ℝ) - 1 - (i : ℕ) := by
      have := i.2
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
    have : (q : ℝ) ^ (((c : ℝ) - 1) / 2 - σ) =
        (q : ℝ) ^ (c - 1 - i : ℕ) * (q : ℝ) ^ ((i : ℕ) - ((c : ℝ) - 1) / 2 - σ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hqR, e]
      congr 1; ring
    rw [this]
    simp only [y]
    push_cast
    ring
  have hrow := fun i : Fin c => sum_sigma_geom
    (fun n => {j : Fin c // i < j} → 𝒪[F] ⧸ Ideal.span {π ^ n}) (q ^ (c - 1 - i))
    (fun n => by
      rw [Nat.card_fun, hcard, ← pow_mul, ← pow_mul, mul_comm]
      congr 2
      rw [← Fin.card_Ioi, ← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun j => Finset.mem_Ioi.symm)) (y i)
    (by
      rw [hy, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hqR.le _)]
      exact hσ i)
  obtain ⟨hs, ht⟩ := sum_pi_prod c (fun i => Row π i) (fun i x => y i ^ x.1) fun i => (hrow i).1
  have hO : IsOpen ((𝒪[F] : Subring F) : Set F) := Valuation.isOpen_integer
  have main := integral_cosets (GlobalTheory.CompanionTheory.QL.GLint 𝒪[F] c) (isOpen_GLint _ hO c).measurableSet κ h1 g
    (fun p p' h => by
      obtain ⟨k, k', hk, hk'⟩ := (hK _ _).1 h
      rw [hg, hg, ← map_mul] at hk hk'
      exact hnf_unique hπ p p' k k' (hι hk) (hι hk'))
    (fun g => φ g * ((nrm (g : Matrix (Fin c) (Fin c) F).det ^ σ : ℝ) : ℂ))
    (fun p => ∏ i, y i ^ (p i).1)
    (fun p k hk => by
      rw [hφ (g p) (htri p) k hk, Units.val_mul, Matrix.det_mul, map_mul, hdetK k hk, mul_one, hg,
        hdet, map_prod, ← Real.finsetProd_rpow _ _ (fun _ _ => nrm.nonneg _), Complex.ofReal_prod,
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hn : nrm (ϖ ^ (p i).1) = (q : ℝ) ^ (-((p i).1 : ℤ)) := by
        rw [map_pow, hpi, inv_pow, _root_.zpow_neg, zpow_natCast]
      rw [hdiag, hχ.2 i _ _ hn, hn, zpow_natCast, mul_pow, mul_assoc, ← Complex.ofReal_mul,
        ← Complex.ofReal_pow, ← Real.rpow_intCast, ← Real.rpow_mul hqR.le, ← Real.rpow_mul hqR.le,
        ← Real.rpow_add hqR, ← Real.rpow_mul_natCast hqR.le]
      congr 3
      push_cast
      ring)
    hs (GlobalTheory.CompanionTheory.QL.Mint 𝒪[F] c)
    (fun x => by
      change GlobalTheory.CompanionTheory.QL.IsInt _ _ ↔ _
      rw [isInt_iff]
      constructor
      · rintro ⟨G, hG⟩
        have hG0 : G.det ≠ 0 := fun h => by
          have := x.det_ne_zero
          rw [← hG, ← RingHom.map_det, h, map_zero] at this
          exact this rfl
        obtain ⟨p, k, k', hk, hk'⟩ := hnf_exists hπ G hG0
        refine ⟨p, (hK _ _).2 ⟨k', k, ?_, ?_⟩⟩
        · rw [hg, ← map_mul, ← hk', ← hG]
        · rw [hg, hk, map_mul, ← hG]
      · rintro ⟨p, h⟩
        obtain ⟨k, k', hk, -⟩ := (hK _ _).1 h
        exact ⟨hnf π p * k, by rw [hk, hg, ← map_mul]⟩)
  refine ⟨main.1, ?_⟩
  rw [main.2, ht]
  exact Finset.prod_congr rfl fun i _ => by rw [(hrow i).2, hy]
end UpperTheory.Reformulated.B.SphericalZetaCosets
