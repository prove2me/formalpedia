-- Prove2me | solution 1 for UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.exists_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:48:15.762904+00:00
-- url     : https://prove2.me/submissions/45dc897b-ac6e-4815-8efc-755588921d49

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormSubgroupOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace UpperTheory.Reformulated.B.WittVectorTrivializingMatrix
private lemma sum_shift {G : Type} [Group G] (N : Subgroup G) [Fintype (G ⧸ N)] {X : Type}
    [AddCommMonoid X] (F : G → X) (hF : ∀ g, ∀ ν ∈ N, F (g * ν) = F g) (h : G) :
    ∑ q : G ⧸ N, F (h * q.out) = ∑ q : G ⧸ N, F q.out := by
  refine Fintype.sum_equiv (MulAction.toPerm h) _ _ fun q => ?_
  obtain ⟨ν, hν⟩ := QuotientGroup.mk_out_eq_mul N (h * q.out)
  have : (MulAction.toPerm h) q = ((h * q.out : G) : G ⧸ N) := by
    have := MulAction.Quotient.mk_smul_out N h q
    simpa using this.symm
  rw [this, hν, hF _ _ ν.2]
private lemma avg {G A C : Type} [Group G] [CommRing A] [CommRing C] {r : ℕ}
    (σ : G → A →+* A) (hσ : ∀ g h x, σ (g * h) x = σ g (σ h x))
    (P : G → Matrix (Fin r) (Fin r) A) (hP : ∀ g h, P (g * h) = P g * P h)
    (hfix : ∀ g h, (P h).map (σ g) = P h) (τ : A →+* C) (N : Subgroup G) [Fintype (G ⧸ N)]
    (hN : ∀ ν ∈ N, (P ν).map τ = 1) (B : Matrix (Fin r) (Fin r) A)
    (hB : ∀ ν ∈ N, B.map (σ ν) = B) (h : G) :
    (P h * (∑ q : G ⧸ N, P q.out * B.map (σ q.out)).map (σ h)).map τ
      = (∑ q : G ⧸ N, P q.out * B.map (σ q.out)).map τ := by
  have hm : ∀ g k, B.map (σ (g * k)) = (B.map (σ k)).map (σ g) := by
    intro g k; ext i j; simp [hσ]
  have h1 : P h * (∑ q : G ⧸ N, P q.out * B.map (σ q.out)).map (σ h)
      = ∑ q : G ⧸ N, P (h * q.out) * B.map (σ (h * q.out)) := by
    rw [← RingHom.mapMatrix_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_mul, hfix, hP, hm, Matrix.mul_assoc]
  rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_sum, map_sum]
  refine sum_shift N (fun g => τ.mapMatrix (P g * B.map (σ g))) (fun g ν hν => ?_) h
  simp only [RingHom.mapMatrix_apply]
  rw [hm, hB ν hν, hP, Matrix.map_mul, Matrix.map_mul, hN ν hν, Matrix.mul_one, Matrix.map_mul]
private lemma dedekind {T L Q : Type} [CommRing T] [CommRing L] [IsDomain L] [Fintype Q]
    (χ : Q → T →+* L) (hχ : Function.Injective χ) (c : Q → L)
    (hc : ∀ a, ∑ q, c q * χ q a = 0) (q : Q) : c q = 0 := by
  have hinj : Function.Injective (fun q => (χ q).toMonoidHom) := by
    intro a b hab
    apply hχ
    ext x
    exact DFunLike.congr_fun hab x
  have := (linearIndependent_monoidHom T L).comp _ hinj
  rw [Fintype.linearIndependent_iff] at this
  apply this c
  funext a
  simpa [Finset.sum_apply] using hc a
private lemma det_field {T L Q : Type} [CommRing T] [Field L] [Fintype Q] {r : ℕ}
    (χ : Q → T →+* L) (hχ : Function.Injective χ) (P : Q → Matrix (Fin r) (Fin r) L)
    (q0 : Q) (P' : Matrix (Fin r) (Fin r) L) (hP : P q0 * P' = 1) :
    ∃ B : Matrix (Fin r) (Fin r) T, (∑ q, P q * B.map (χ q)).det ≠ 0 := by
  classical
  let v : (Fin r → T) → (Fin r → L) := fun x => ∑ q, (P q).mulVec (χ q ∘ x)
  have hspan : Submodule.span L (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hcol : ∀ j, f ((P q0).mulVec (Pi.single j 1)) = 0 := by
      intro j
      refine dedekind χ hχ (fun q => f ((P q).mulVec (Pi.single j 1))) (fun a => ?_) q0
      have h1 : f (v (Pi.single j a)) = 0 :=
        hf (Submodule.subset_span ⟨_, rfl⟩)
      rw [← h1]
      simp only [v, map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      have : (χ q ∘ (Pi.single j a : Fin r → T)) = χ q a • (Pi.single j 1 : Fin r → L) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp
        · simp [hi]
      rw [this, Matrix.mulVec_smul, map_smul, smul_eq_mul, mul_comm]
    apply hf0
    refine LinearMap.ext fun w => ?_
    have hw : w = (P q0).mulVec (P'.mulVec w) := by
      rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
    rw [hw]
    generalize P'.mulVec w = u
    have hu : u = ∑ j, u j • (Pi.single j 1 : Fin r → L) := by
      funext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [hu, Matrix.mulVec_sum, map_sum]
    simp only [Matrix.mulVec_smul, map_smul, hcol]
    simp
  have hex : ∃ f : Fin r → (Fin r → L), (∀ i, f i ∈ Set.range v) ∧ LinearIndependent L f := by
    obtain ⟨f, h1, -, h3⟩ := Submodule.exists_fun_fin_finrank_span_eq L (Set.range v)
    have hr : Module.finrank L (Submodule.span L (Set.range v)) = r := by
      rw [hspan]; simp
    exact ⟨f ∘ Fin.cast hr.symm, fun i => h1 _, h3.comp _ (Fin.cast_injective _)⟩
  obtain ⟨f, h1, h2⟩ := hex
  choose x hx using h1
  refine ⟨Matrix.of fun i j => x j i, ?_⟩
  have : (∑ q, P q * (Matrix.of fun i j => x j i).map (χ q)).col = f := by
    funext j i
    rw [← hx j]
    simp [v, Matrix.col, Matrix.sum_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Finset.sum_apply]
  rw [← this, Matrix.linearIndependent_cols_iff_isUnit, Matrix.isUnit_iff_isUnit_det] at h2
  exact h2.ne_zero
private lemma det_domain {T R Q : Type} [CommRing T] [CommRing R] [IsDomain R] [Fintype Q] {r : ℕ}
    (χ : Q → T →+* R) (hχ : Function.Injective χ) (P : Q → Matrix (Fin r) (Fin r) R)
    (q0 : Q) (P' : Matrix (Fin r) (Fin r) R) (hP : P q0 * P' = 1) :
    ∃ B : Matrix (Fin r) (Fin r) T, (∑ q, P q * B.map (χ q)).det ≠ 0 := by
  let ι := algebraMap R (FractionRing R)
  have hι : Function.Injective ι := IsFractionRing.injective R (FractionRing R)
  obtain ⟨B, hB⟩ := det_field (fun q => ι.comp (χ q)) (fun a b hab => hχ (by
      ext x; exact hι (DFunLike.congr_fun hab x))) (fun q => (P q).map ι) q0 (P'.map ι) (by
      rw [← Matrix.map_mul, hP]; simp)
  refine ⟨B, fun h => hB ?_⟩
  have : (∑ q, (P q).map ι * B.map (ι.comp (χ q))) = ι.mapMatrix (∑ q, P q * B.map (χ q)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [RingHom.mapMatrix_apply, Matrix.map_mul]; rfl
  rw [this, ← RingHom.map_det, h, map_zero]
section
variable {p : ℕ} [hp : Fact (Nat.Prime p)] {G : Type} [Group G] {R : Type} [CommRing R]
private lemma per_mul {p m : ℕ} {y : R} (h : y ^ p ^ m = y) (k : ℕ) : y ^ p ^ (m * k) = y := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, h]
private lemma sg_coeff (ρ : G →* R ≃+* R) (g : G) (x : WittVector p R) (i : ℕ) :
    (sg p ρ g x).coeff i = ρ g (x.coeff i) := by
  simp [sg, WittVector.map_coeff]
private lemma sg_mul (ρ : G →* R ≃+* R) (g h : G) (x : WittVector p R) :
    sg p ρ (g * h) x = sg p ρ g (sg p ρ h x) := by
  ext i; simp [sg_coeff]
private lemma trunc_iff (n : ℕ) (x y : WittVector p R) :
    WittVector.truncate n x = WittVector.truncate n y ↔ ∀ i < n, x.coeff i = y.coeff i := by
  constructor
  · intro h i hi
    rw [← WittVector.coeff_truncate x ⟨i, hi⟩, ← WittVector.coeff_truncate y ⟨i, hi⟩, h]
  · intro h
    ext i
    simp [WittVector.coeff_truncate, h i i.2]
variable [CharP R p]
private lemma map_zl (f : R →+* R) (x : ℤ_[p]) : WittVector.map f (zlW p R x) = zlW p R x := by
  ext i
  simp only [zlW, RingHom.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod (f.comp (ZMod.castHom (dvd_refl p) R))
    (ZMod.castHom (dvd_refl p) R)) _
private lemma mem_Km (m : ℕ) (y : R) : y ∈ Km p R m ↔ y ^ p ^ m = y := by
  simp [Km, iterateFrobenius_def]
private lemma mem_Sm' (m : ℕ) (x : WittVector p R) :
    x ∈ Sm p R m ↔ WittVector.map (iterateFrobenius R p m) x = x := Iff.rfl
private lemma mem_Sm (m : ℕ) (x : WittVector p R) :
    x ∈ Sm p R m ↔ ∀ i, x.coeff i ^ p ^ m = x.coeff i := by
  rw [mem_Sm', WittVector.ext_iff]
  simp [WittVector.map_coeff, iterateFrobenius_def]
private lemma zl_mem (m : ℕ) (x : ℤ_[p]) : zlW p R x ∈ Sm p R m := map_zl _ x
private lemma sg_mem (ρ : G →* R ≃+* R) (g : G) {m : ℕ} {x : WittVector p R} (h : x ∈ Sm p R m) :
    sg p ρ g x ∈ Sm p R m := by
  rw [mem_Sm] at h ⊢
  intro i
  rw [sg_coeff, ← map_pow, h]
private lemma sg_fix (ρ : G →* R ≃+* R) {g : G} {m : ℕ} (hg : g ∈ Nm ρ p m) {x : WittVector p R}
    (h : x ∈ Sm p R m) : sg p ρ g x = x := by
  rw [mem_Sm] at h
  ext i
  rw [sg_coeff, hg _ (h i)]
private lemma teich_mem {m : ℕ} {a : R} (ha : a ^ p ^ m = a) :
    WittVector.teichmuller p a ∈ Sm p R m := by
  rw [mem_Sm', WittVector.map_teichmuller, iterateFrobenius_def, ha]
private lemma unit_of_coeff {x : WittVector p R} (h : IsUnit (x.coeff 0)) : IsUnit x := by
  obtain ⟨u, hu⟩ := h
  exact ⟨WittVector.mkUnit hu.symm, WittVector.coe_mkUnit _⟩
variable [IsDomain R]
omit [CharP R p] in
private lemma unit_of_per {m : ℕ} (hm : 0 < m) {y : R} (hy : y ^ p ^ m = y) (h0 : y ≠ 0) :
    IsUnit y := by
  have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
  obtain ⟨k, hk⟩ : ∃ k, p ^ m = k + 2 := ⟨p ^ m - 2, by omega⟩
  rw [hk] at hy
  have : y * y ^ k = 1 := by
    apply mul_left_cancel₀ h0
    rw [mul_one]
    conv_rhs => rw [← hy]
    ring
  exact IsUnit.of_mul_eq_one _ this
omit [IsDomain R] in
private lemma chi_apply (ρ : G →* R ≃+* R) (m : ℕ) (q : G ⧸ Nm ρ p m) (a : Km p R m) :
    chi ρ p m q a = ρ q.out a := rfl
omit [IsDomain R] in
private lemma chi_inj (ρ : G →* R ≃+* R) (m : ℕ) : Function.Injective (chi ρ p m) := by
  intro a b hab
  rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b, QuotientGroup.eq]
  intro y hy
  have := DFunLike.congr_fun hab ⟨y, (mem_Km m y).2 hy⟩
  simp only [chi_apply] at this
  rw [map_mul]
  change ρ a.out⁻¹ (ρ b.out y) = y
  rw [← this]
  change (ρ a.out⁻¹ * ρ a.out) y = y
  rw [← map_mul, inv_mul_cancel, map_one]; rfl
private lemma free_etale_sheaf_zmod_exists_hom_sending_generator (ρ : G →* R ≃+* R) {m : ℕ} (hm : 0 < m) [Fintype (G ⧸ Nm ρ p m)] :
    ∃ t ∈ Sm p R m, ∑ q : G ⧸ Nm ρ p m, sg p ρ q.out t = 1 := by
  obtain ⟨a, ha⟩ : ∃ a : Km p R m, ∑ q : G ⧸ Nm ρ p m, (1 : R) * chi ρ p m q a ≠ 0 := by
    by_contra h
    push Not at h
    exact one_ne_zero (dedekind (chi ρ p m) (chi_inj ρ m) (fun _ => (1 : R)) h ((1 : G) : _))
  have hT : WittVector.teichmuller p (a : R) ∈ Sm p R m := teich_mem ((mem_Km m _).1 a.2)
  set T := WittVector.teichmuller p (a : R) with hTd
  set s := ∑ q : G ⧸ Nm ρ p m, sg p ρ q.out T with hs
  have hsS : s ∈ Sm p R m := Subring.sum_mem _ fun q _ => sg_mem ρ _ hT
  have hs0 : s.coeff 0 ≠ 0 := by
    rw [← WittVector.constantCoeff_apply, hs, map_sum]
    simpa [sg_coeff, hTd, chi_apply] using ha
  obtain ⟨u, hu⟩ : IsUnit s := unit_of_coeff (unit_of_per hm ((mem_Sm m s).1 hsS 0) hs0)
  have hinv : ∀ φ : WittVector p R →+* WittVector p R, φ s = s → φ (↑u⁻¹) = ↑u⁻¹ := by
    intro φ hφ
    have h1 : s * φ (↑u⁻¹) = 1 := by
      rw [← hφ, ← map_mul, ← hu, Units.mul_inv, map_one]
    rw [← hu] at h1
    exact (Units.inv_eq_of_mul_eq_one_right h1).symm
  have hfix : ∀ g, sg p ρ g s = s := by
    intro g
    rw [hs, map_sum]
    simp only [← sg_mul]
    exact sum_shift (Nm ρ p m) (fun g => sg p ρ g T)
      (fun g ν hν => by simp only [sg_mul, sg_fix ρ hν hT]) g
  refine ⟨T * ↑u⁻¹, Subring.mul_mem _ hT (hinv _ hsS), ?_⟩
  simp only [map_mul, hinv _ (hfix _)]
  rw [← Finset.sum_mul, ← hs, ← hu, Units.mul_inv]
omit [IsDomain R] in
private lemma Mw_mul {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (g h : G) :
    Mw p R M (g * h) = Mw p R M g * Mw p R M h := by
  simp only [Mw, map_mul, Matrix.map_mul]
omit [IsDomain R] in
private lemma Mw_one {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) :
    Mw p R M 1 = 1 := by
  simp [Mw]
omit [IsDomain R] in
private lemma good_avg (ρ : G →* R ≃+* R) {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p])
    {n m : ℕ} (hm : 0 < m) [Fintype (G ⧸ Nm ρ p m)]
    (hN : ∀ ν ∈ Nm ρ p m, (Mw p R M ν).map (WittVector.truncate n) = 1)
    (B : Matrix (Fin r) (Fin r) (WittVector p R)) (hB : ∀ i j, B i j ∈ Sm p R m) :
    Good ρ M n (∑ q : G ⧸ Nm ρ p m, Mw p R M q.out * B.map (sg p ρ q.out)) ∧
      ∀ i j, (∑ q : G ⧸ Nm ρ p m, Mw p R M q.out * B.map (sg p ρ q.out)) i j ∈ Sm p R m := by
  have h1 : ∀ i j, (∑ q : G ⧸ Nm ρ p m, Mw p R M q.out * B.map (sg p ρ q.out)) i j ∈ Sm p R m := by
    intro i j
    rw [Matrix.sum_apply]
    refine Subring.sum_mem _ fun q _ => ?_
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (zl_mem _ _) (sg_mem ρ _ (hB _ _))
  refine ⟨⟨⟨m, hm, h1⟩, fun g => ?_⟩, h1⟩
  refine avg (sg p ρ) (sg_mul ρ) (Mw p R M) (Mw_mul M) (fun g h => ?_) _ (Nm ρ p m) hN B
    (fun ν hν => ?_) g
  · ext1 i j
    exact map_zl _ _
  · ext1 i j
    exact sg_fix ρ hν (hB i j)
private lemma step (ρ : G →* R ≃+* R) {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p])
    (hfin : ∀ m, 0 < m → Finite (G ⧸ Nm ρ p m)) (n : ℕ)
    (hlev : ∃ m, 0 < m ∧ ∀ ν ∈ Nm ρ p m, (Mw p R M ν).map (WittVector.truncate (n + 1)) = 1)
    (W : Matrix (Fin r) (Fin r) (WittVector p R)) (hW : Good ρ M n W) :
    ∃ W', Good ρ M (n + 1) W' ∧ W'.map (WittVector.truncate n) = W.map (WittVector.truncate n) := by
  obtain ⟨a, ha, hN⟩ := hlev
  obtain ⟨⟨b, hb, hS⟩, hW⟩ := hW
  have hm : 0 < a * b := Nat.mul_pos ha hb
  haveI := hfin _ hm
  haveI := Fintype.ofFinite (G ⧸ Nm ρ p (a * b))
  obtain ⟨t, ht, ht1⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator (p := p) ρ hm
  have hS' : ∀ i j, W i j ∈ Sm p R (a * b) := by
    intro i j
    have := hS i j
    rw [mem_Sm] at this ⊢
    intro k
    rw [mul_comm]
    exact per_mul (this k) a
  refine ⟨_, (good_avg ρ M hm (fun ν hν => hN ν fun y hy => hν y (per_mul hy b)) (t • W)
    (fun i j => Subring.mul_mem _ ht (hS' i j))).1, ?_⟩
  have h1 : ∀ g, (Mw p R M g * (t • W).map (sg p ρ g)).map (WittVector.truncate n)
      = WittVector.truncate n (sg p ρ g t) • W.map (WittVector.truncate n) := by
    intro g
    have : (t • W).map (sg p ρ g) = sg p ρ g t • W.map (sg p ρ g) := by
      ext1 i j; simp
    rw [this, Matrix.mul_smul, ← hW g]
    ext1 i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [← RingHom.mapMatrix_apply, map_sum]
  simp only [RingHom.mapMatrix_apply, h1]
  rw [← Finset.sum_smul, ← map_sum, ht1, map_one, one_smul]
private lemma base (ρ : G →* R ≃+* R) {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p])
    (hfin : ∀ m, 0 < m → Finite (G ⧸ Nm ρ p m))
    (hlev : ∃ m, 0 < m ∧ ∀ ν ∈ Nm ρ p m, (Mw p R M ν).map (WittVector.truncate 1) = 1) :
    ∃ W, Good ρ M 1 W ∧ IsUnit (W.det.coeff 0) := by
  obtain ⟨m, hm, hN⟩ := hlev
  haveI := hfin _ hm
  haveI := Fintype.ofFinite (G ⧸ Nm ρ p m)
  let c : WittVector p R →+* R := WittVector.constantCoeff
  let q0 : G ⧸ Nm ρ p m := ((1 : G) : _)
  obtain ⟨B, hB⟩ := det_domain (chi ρ p m) (chi_inj ρ m) (fun q => (Mw p R M q.out).map c) q0
    ((Mw p R M q0.out⁻¹).map c) (by
      rw [← Matrix.map_mul, ← Mw_mul, mul_inv_cancel, Mw_one]; simp)
  obtain ⟨h1, h2⟩ := good_avg ρ M hm hN (B.map fun a => WittVector.teichmuller p (a : R))
    (fun i j => teich_mem ((mem_Km m _).1 (B i j).2))
  refine ⟨_, h1, unit_of_per hm ((mem_Sm m _).1 ?_ 0) ?_⟩
  · rw [Matrix.det_apply']
    exact Subring.sum_mem _ fun s _ => Subring.mul_mem _ (intCast_mem _ _)
      (Subring.prod_mem _ fun i _ => h2 _ _)
  · rw [← WittVector.constantCoeff_apply, RingHom.map_det, map_sum]
    convert hB using 3 with q
    rw [RingHom.mapMatrix_apply, Matrix.map_mul]
    refine congrArg₂ (· * ·) rfl ?_
    ext i j
    simp [sg_coeff, chi_apply]
private lemma core (ρ : G →* R ≃+* R) {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p])
    (hfin : ∀ m, 0 < m → Finite (G ⧸ Nm ρ p m))
    (hlev : ∀ n, ∃ m, 0 < m ∧ ∀ ν ∈ Nm ρ p m, (Mw p R M ν).map (WittVector.truncate n) = 1) :
    ∃ W : Matrix (Fin r) (Fin r) (WittVector p R), IsUnit W.det ∧
      ∀ (g : G) (f : R →+* R), (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → f y = ρ g y) →
        Mw p R M g * W.map (WittVector.map f) = W := by
  obtain ⟨W0, hW0, hd⟩ := base ρ M hfin (hlev 1)
  choose F hF1 hF2 using fun n => step ρ M hfin (n + 1) (hlev _)
  let s : ∀ n : ℕ, {W // Good ρ M (n + 1) W} := fun n =>
    Nat.rec ⟨W0, hW0⟩ (fun n w => ⟨F n w.1 w.2, hF1 n w.1 w.2⟩) n
  have hs0 : (s 0).1 = W0 := rfl
  have hs : ∀ n i j k, k < n + 1 → ((s (n + 1)).1 i j).coeff k = ((s n).1 i j).coeff k := by
    intro n i j
    rw [← trunc_iff]
    exact congrFun (congrFun (hF2 n (s n).1 (s n).2) i) j
  have hs' : ∀ i j k n, k ≤ n → ((s n).1 i j).coeff k = ((s k).1 i j).coeff k := by
    intro i j k n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih => rw [hs n i j k (by omega), ih]
  let W : Matrix (Fin r) (Fin r) (WittVector p R) :=
    fun i j => WittVector.mk p fun k => ((s k).1 i j).coeff k
  have hW : ∀ i j k, (W i j).coeff k = ((s k).1 i j).coeff k := fun _ _ _ => rfl
  refine ⟨W, unit_of_coeff ?_, fun g f hf => ?_⟩
  · rw [← WittVector.constantCoeff_apply, RingHom.map_det] at hd ⊢
    convert hd using 2
    ext i j
    simp [hW, hs0]
  · have key : ∀ n, (Mw p R M g * W.map (WittVector.map f)).map (WittVector.truncate (n + 1))
        = W.map (WittVector.truncate (n + 1)) := by
      intro n
      obtain ⟨⟨m, hm, hS⟩, hG⟩ := (s n).2
      have e1 : W.map (WittVector.truncate (n + 1)) = (s n).1.map (WittVector.truncate (n + 1)) := by
        ext1 i j
        simp only [Matrix.map_apply]
        rw [trunc_iff]
        intro k hk
        rw [hW, hs' i j k n (by omega)]
      have e2 : (W.map (WittVector.map f)).map (WittVector.truncate (n + 1))
          = ((s n).1.map (sg p ρ g)).map (WittVector.truncate (n + 1)) := by
        ext1 i j
        simp only [Matrix.map_apply]
        rw [trunc_iff]
        intro k hk
        rw [WittVector.map_coeff, sg_coeff, hW, ← hs' i j k n (by omega)]
        exact hf m hm _ ((mem_Sm m _).1 (hS i j) k)
      rw [e1, ← hG g, Matrix.map_mul, Matrix.map_mul, e2]
    ext i j k
    exact (trunc_iff (k + 1) _ _).1 (congrFun (congrFun (key k) i) j) k (Nat.lt_succ_self k)
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
omit [CharP R p] [CompactSpace G] in
private lemma Nm_open (ρ : G →* R ≃+* R)
    (h : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ (g : G) in nhds (1 : G), ρ g y = y)
    {m : ℕ} (hm : 0 < m) : IsOpen (Nm ρ p m : Set G) := by
  classical
  have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
  have hfin : {y : R | y ^ p ^ m = y}.Finite := by
    have hne : (Polynomial.X ^ p ^ m - Polynomial.X : Polynomial R) ≠ 0 :=
      by
      intro h0
      have h2 := congrArg Polynomial.natDegree (sub_eq_zero.1 h0)
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] at h2
      omega
    refine (Polynomial.roots (Polynomial.X ^ p ^ m - Polynomial.X : Polynomial R)).toFinset.finite_toSet.subset ?_
    intro y hy
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hne]
    simpa [sub_eq_zero] using hy
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  exact (Filter.eventually_all_finite hfin).2 fun y hy => h y m hm hy
private lemma level (ρ : G →* R ≃+* R)
    (h : ∀ (y : R) (m : ℕ), 0 < m → y ^ p ^ m = y → ∀ᶠ (g : G) in nhds (1 : G), ρ g y = y)
    {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]) (hc : Continuous M)
    (hM : ∀ g : G, (∀ m, 0 < m → ∀ y : R, y ^ p ^ m = y → ρ g y = y) → M g = 1) (n : ℕ) :
    ∃ m, 0 < m ∧ ∀ ν ∈ Nm ρ p m, (Mw p R M ν).map (WittVector.truncate n) = 1 := by
  let U : Set G := ⋂ i, ⋂ j, {g | ‖M g i j - (1 : Matrix (Fin r) (Fin r) ℤ_[p]) i j‖
    < (p : ℝ) ^ (-(n : ℤ) + 1)}
  have hU : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact isOpen_lt (((hc.matrix_elem i j).sub continuous_const).norm) continuous_const
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  obtain ⟨m, hm⟩ := hU.isClosed_compl.isCompact.elim_directed_family_closed
    (fun m : ℕ+ => (Nm ρ p m : Set G))
    (fun m => Subgroup.isClosed_of_isOpen _ (Nm_open ρ h m.2))
    (by
      rw [← Set.disjoint_iff_inter_eq_empty, Set.disjoint_left]
      intro g hg hg'
      apply hg
      rw [Set.mem_iInter] at hg'
      have := hM g fun m hm => hg' ⟨m, hm⟩
      simp only [U, Set.mem_iInter, Set.mem_setOf_eq, this, sub_self, norm_zero]
      intro i j
      positivity)
    (fun a b => ⟨a * b, fun g hg y hy => hg y (per_mul hy b), fun g hg y hy => hg y (by
      rw [mul_comm]; exact per_mul hy a)⟩)
  refine ⟨m, m.2, fun ν hν => ?_⟩
  have hν' : ν ∈ U := by
    by_contra hn
    exact Set.disjoint_left.1 (Set.disjoint_iff_inter_eq_empty.2 hm) hn hν
  simp only [U, Set.mem_iInter, Set.mem_setOf_eq] at hν'
  ext1 i j
  have := hν' i j
  rw [← PadicInt.norm_le_pow_iff_norm_lt_pow_add_one, PadicInt.norm_le_pow_iff_mem_span_pow,
    Ideal.mem_span_singleton'] at this
  obtain ⟨c, hc⟩ := this
  have e : M ν i j = (1 : Matrix (Fin r) (Fin r) ℤ_[p]) i j + c * (p : ℤ_[p]) ^ n := by
    rw [hc]; ring
  have z : WittVector.truncate n (zlW p R c * (p : WittVector p R) ^ n) = 0 := by
    rw [← RingHom.mem_ker, WittVector.mem_ker_truncate]
    intro k hk
    exact WittVector.mul_pow_charP_coeff_zero _ hk
  simp only [Mw, Matrix.map_apply]
  rw [e, map_add, map_mul, map_pow, map_natCast, map_add, z, add_zero]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]
end
end UpperTheory.Reformulated.B.WittVectorTrivializingMatrix
end

set_option autoImplicit false

namespace UpperTheory.Reformulated.B.WittVectorTrivializingMatrix
theorem _root_.solution :
    ∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {G : Type} [inst : Group G] {R : Type} [inst_1 : CommRing R] (ρ : G →* R ≃+* R)
      [inst_2 : TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [IsDomain R] [inst_6 : CharP R p],
      (∀ (y : R) (m : ℕ), (0 : ℕ) < m → y ^ p ^ m = y → ∀ᶠ (g : G) in nhds (1 : G), ((ρ : G → R ≃+* R) g : R → R) y = y) →
        ∀ {r : ℕ} (M : G →* Matrix (Fin r) (Fin r) ℤ_[p]),
          Continuous (⇑M : G → Matrix (Fin r) (Fin r) ℤ_[p]) →
            (∀ (g : G),
                (∀ (m : ℕ), (0 : ℕ) < m → ∀ (y : R), y ^ p ^ m = y → ((ρ : G → R ≃+* R) g : R → R) y = y) →
                  (M : G → Matrix (Fin r) (Fin r) ℤ_[p]) g = (1 : Matrix (Fin r) (Fin r) ℤ_[p])) →
              ∃ (W : Matrix (Fin r) (Fin r) (WittVector p R)),
                IsUnit W.det ∧
                  ∀ (g : G) (f : R →+* R),
                    (∀ (m : ℕ), (0 : ℕ) < m → ∀ (y : R), y ^ p ^ m = y → (f : R → R) y = ((ρ : G → R ≃+* R) g : R → R) y) →
                      ((M : G → Matrix (Fin r) (Fin r) ℤ_[p]) g).map (⇑(UpperTheory.Reformulated.B.WittVectorTrivializingMatrix.zlW p R) : ℤ_[p] → WittVector p R) *
                          W.map (⇑(WittVector.map f) : WittVector p R → WittVector p R) =
                        W := by
  intro p hp G _ R _ ρ _ _ _ _ _ h r M hc hM
  exact core ρ M
    (fun m hm => Subgroup.quotient_finite_of_isOpen _ (Nm_open ρ h hm)) (level ρ h M hc hM)
end UpperTheory.Reformulated.B.WittVectorTrivializingMatrix
