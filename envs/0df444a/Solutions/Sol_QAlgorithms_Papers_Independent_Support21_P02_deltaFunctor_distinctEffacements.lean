-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P02.deltaFunctor_distinctEffacements
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T04:38:03.977381+00:00
-- url     : https://prove2.me/submissions/6947c1e2-6087-4cf5-9f7f-131d5dff8137

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P02
universe u v w

open CategoryTheory QAlgorithms.Papers.Independent.Support21.P02

noncomputable section

theorem g66e_zero_elt {X : AddCommGrpCat.{w}} (h : Limits.IsZero X) (x : X) : x = 0 := by
  have h1 := h.eq_of_src (𝟙 X) 0
  have h2 := congrArg (fun f : X ⟶ X => f.hom x) h1
  simpa using h2

theorem g66e_capp {X Y Z : AddCommGrpCat.{w}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    (f ≫ g).hom x = g.hom (f.hom x) := rfl

variable {C : Type u} [Category.{v} C] {S : SequenceClass C}

theorem g66e_surj (R : FunctorialResolution S) (H : DeltaFunctor.{u, v, w} S) (A : C) (n : ℕ)
    (hz : Limits.IsZero ((H.degree (n+1)).obj (R.I.obj A))) :
    Function.Surjective (H.connecting (R.sequence A) n).hom := by
  intro b
  exact (H.exact_left_positive (R.sequence A) n b).1 (g66e_zero_elt hz _)

theorem g66e_surj2 (R : FunctorialResolution S) (H : DeltaFunctor.{u, v, w} S) (A : C) (n : ℕ)
    (hz : Limits.IsZero ((H.degree (n+1)).obj (R.I.obj A))) (x : (H.degree (n+1)).obj A) :
    ∃ y : (H.degree n).obj (R.U.obj A), (H.connecting (R.sequence A) n).hom y = x :=
  g66e_surj R H A n hz x

/-- the step map at A -/
def g66e_stepApp (R : FunctorialResolution S) (H K : DeltaFunctor.{u, v, w} S) (n : ℕ)
    (phi : H.degree n ⟶ K.degree n)
    (hz : ∀ A, Limits.IsZero ((H.degree (n+1)).obj (R.I.obj A))) (A : C) :
    (H.degree (n+1)).obj A ⟶ (K.degree (n+1)).obj A :=
  AddCommGrpCat.ofHom
    ((H.connecting (R.sequence A) n).hom.liftOfSurjective (g66e_surj R H A n (hz A))
      ⟨(K.connecting (R.sequence A) n).hom.comp (phi.app (R.U.obj A)).hom, by
        intro x hx
        have hx' : (H.connecting (R.sequence A) n).hom x = 0 := hx
        obtain ⟨y, rfl⟩ := (H.exact_right (R.sequence A) n x).1 hx'
        have hn : (phi.app (R.U.obj A)).hom (((H.degree n).map (R.zeta.app A)).hom y) =
            ((K.degree n).map (R.zeta.app A)).hom ((phi.app (R.I.obj A)).hom y) :=
          congrArg (fun f => f.hom y) (phi.naturality (R.zeta.app A))
        refine AddMonoidHom.mem_ker.2 ?_
        change (K.connecting (R.sequence A) n).hom
          ((phi.app (R.U.obj A)).hom (((H.degree n).map (R.zeta.app A)).hom y)) = 0
        rw [hn]
        exact (K.exact_right (R.sequence A) n _).2 ⟨_, rfl⟩⟩)

theorem g66e_stepApp_spec (R : FunctorialResolution S) (H K : DeltaFunctor.{u, v, w} S) (n : ℕ)
    (phi : H.degree n ⟶ K.degree n)
    (hz : ∀ A, Limits.IsZero ((H.degree (n+1)).obj (R.I.obj A))) (A : C)
    (y : (H.degree n).obj (R.U.obj A)) :
    (g66e_stepApp R H K n phi hz A).hom ((H.connecting (R.sequence A) n).hom y) =
      (K.connecting (R.sequence A) n).hom ((phi.app (R.U.obj A)).hom y) := by
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ y

def g66e_step (R : FunctorialResolution S) (H K : DeltaFunctor.{u, v, w} S) (n : ℕ)
    (phi : H.degree n ⟶ K.degree n)
    (hz : ∀ A, Limits.IsZero ((H.degree (n+1)).obj (R.I.obj A))) :
    H.degree (n+1) ⟶ K.degree (n+1) where
  app A := g66e_stepApp R H K n phi hz A
  naturality A A' f := by
    let sm : SequenceMap (R.sequence A) (R.sequence A') :=
      { left := f, middle := R.I.map f, right := R.U.map f
        first_square := (R.iota.naturality f).symm
        second_square := (R.zeta.naturality f).symm }
    have key : ∀ y : (H.degree n).obj (R.U.obj A),
        (g66e_stepApp R H K n phi hz A').hom
          (((H.degree (n + 1)).map f).hom ((H.connecting (R.sequence A) n).hom y)) =
        ((K.degree (n + 1)).map f).hom ((g66e_stepApp R H K n phi hz A).hom
          ((H.connecting (R.sequence A) n).hom y)) := by
      intro y
      have hH := congrArg (fun g => g.hom y) (H.connecting_natural _ _ sm n)
      have hK := congrArg (fun g => g.hom ((phi.app (R.U.obj A)).hom y))
        (K.connecting_natural _ _ sm n)
      have hp := congrArg (fun g => g.hom y) (phi.naturality (R.U.map f))
      rw [g66e_stepApp_spec]
      have e1 : ((H.degree (n + 1)).map f).hom ((H.connecting (R.sequence A) n).hom y) =
          (H.connecting (R.sequence A') n).hom (((H.degree n).map (R.U.map f)).hom y) := hH.symm
      rw [e1, g66e_stepApp_spec]
      exact (congrArg (K.connecting (R.sequence A') n).hom hp).trans hK
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    obtain ⟨y, rfl⟩ := g66e_surj R H A n (hz A) x
    exact key y

theorem g66e_step_sq (R : FunctorialResolution S) (H K : DeltaFunctor.{u, v, w} S) (n : ℕ)
    (phi : H.degree n ⟶ K.degree n)
    (hz : ∀ A, Limits.IsZero ((H.degree (n+1)).obj (R.I.obj A))) (A : C) :
    H.connecting (R.sequence A) n ≫ (g66e_step R H K n phi hz).app A =
      phi.app (R.U.obj A) ≫ K.connecting (R.sequence A) n := by
  apply AddCommGrpCat.hom_ext
  ext y
  exact g66e_stepApp_spec R H K n phi hz A y

theorem g66e_step_unique (R : FunctorialResolution S) (H K : DeltaFunctor.{u, v, w} S) (n : ℕ)
    (phi : H.degree n ⟶ K.degree n)
    (hz : ∀ A, Limits.IsZero ((H.degree (n+1)).obj (R.I.obj A)))
    (a b : H.degree (n+1) ⟶ K.degree (n+1))
    (ha : ∀ A, H.connecting (R.sequence A) n ≫ a.app A =
      phi.app (R.U.obj A) ≫ K.connecting (R.sequence A) n)
    (hb : ∀ A, H.connecting (R.sequence A) n ≫ b.app A =
      phi.app (R.U.obj A) ≫ K.connecting (R.sequence A) n) : a = b := by
  ext A x
  obtain ⟨y, rfl⟩ := g66e_surj R H A n (hz A) x
  have h1 := congrArg (fun g => g.hom y) ((ha A).trans (hb A).symm)
  exact h1

open Classical in
def g66e_fam (R : FunctorialResolution S) (H K : DeltaFunctor.{u, v, w} S)
    (alpha : H.degree 0 ⟶ K.degree 0) : (n : ℕ) → (H.degree n ⟶ K.degree n)
  | 0 => alpha
  | n+1 => if h : ∀ A, Limits.IsZero ((H.degree (n+1)).obj (R.I.obj A)) then
      g66e_step R H K n (g66e_fam R H K alpha n) h else 0

theorem g66e_fam_sq (R : FunctorialResolution S) (H K : DeltaFunctor.{u, v, w} S)
    (alpha : H.degree 0 ⟶ K.degree 0) (n : ℕ)
    (hz : ∀ A, Limits.IsZero ((H.degree (n+1)).obj (R.I.obj A))) (A : C) :
    H.connecting (R.sequence A) n ≫ (g66e_fam R H K alpha (n+1)).app A =
      (g66e_fam R H K alpha n).app (R.U.obj A) ≫ K.connecting (R.sequence A) n := by
  have : g66e_fam R H K alpha (n+1) = g66e_step R H K n (g66e_fam R H K alpha n) hz := by
    simp only [g66e_fam, dif_pos hz]
  rw [this]
  exact g66e_step_sq R H K n _ hz A


theorem g66e_allseq (R : FunctorialResolution S) (H K : DeltaFunctor.{u, v, w} S) (n : ℕ)
    (phi0 : H.degree n ⟶ K.degree n) (phi1 : H.degree (n+1) ⟶ K.degree (n+1))
    (hsq : ∀ A, H.connecting (R.sequence A) n ≫ phi1.app A =
      phi0.app (R.U.obj A) ≫ K.connecting (R.sequence A) n)
    (hz : ∀ A, Limits.IsZero ((H.degree (n+1)).obj (R.I.obj A)))
    (hq : CompatibleQuotients R) (s : DistinguishedSequence S) :
    H.connecting s n ≫ phi1.app s.A = phi0.app s.D ≫ K.connecting s n := by
  obtain ⟨Q, q, beta, gamma, hd, hb, hg⟩ := hq s
  let s' : DistinguishedSequence S := ⟨s.A, R.I.obj s.B, Q, s.first ≫ R.iota.app s.B, q, hd⟩
  let m1 : SequenceMap (R.sequence s.A) s' :=
    { left := 𝟙 _, middle := R.I.map s.first, right := beta
      first_square := by
        have := R.iota.naturality s.first
        simp only [Functor.id_map] at this
        change R.iota.app s.A ≫ R.I.map s.first = 𝟙 _ ≫ (s.first ≫ R.iota.app s.B)
        rw [Category.id_comp, this]
      second_square := hb }
  let m2 : SequenceMap s s' :=
    { left := 𝟙 _, middle := R.iota.app s.B, right := gamma
      first_square := by
        change s.first ≫ R.iota.app s.B = 𝟙 _ ≫ (s.first ≫ R.iota.app s.B)
        rw [Category.id_comp]
      second_square := hg }
  have nat1 : ∀ (F : DeltaFunctor.{u, v, w} S) (y : (F.degree n).obj (R.U.obj s.A)),
      (F.connecting s' n).hom (((F.degree n).map beta).hom y) =
        (F.connecting (R.sequence s.A) n).hom y := by
    intro F y
    have h := congrArg (fun g => g.hom y) (F.connecting_natural _ _ m1 n)
    have h2 : (F.degree (n+1)).map m1.left = 𝟙 _ := (F.degree (n+1)).map_id _
    simp only [h2, Category.comp_id] at h
    exact h
  have nat2 : ∀ (F : DeltaFunctor.{u, v, w} S) (y : (F.degree n).obj s.D),
      (F.connecting s' n).hom (((F.degree n).map gamma).hom y) =
        (F.connecting s n).hom y := by
    intro F y
    have h := congrArg (fun g => g.hom y) (F.connecting_natural _ _ m2 n)
    have h2 : (F.degree (n+1)).map m2.left = 𝟙 _ := (F.degree (n+1)).map_id _
    simp only [h2, Category.comp_id] at h
    exact h
  have main : ∀ z : (H.degree n).obj Q,
      (phi1.app s.A).hom ((H.connecting s' n).hom z) =
        (K.connecting s' n).hom ((phi0.app Q).hom z) := by
    intro z
    obtain ⟨y, hy⟩ := g66e_surj2 R H s.A n (hz s.A) ((H.connecting s' n).hom z)
    have h0 : (H.connecting s' n).hom (z - ((H.degree n).map beta).hom y) = 0 := by
      rw [map_sub, nat1, hy, sub_self]
    obtain ⟨w, hw⟩ := (H.exact_right s' n _).1 h0
    have hzw : z = ((H.degree n).map beta).hom y + ((H.degree n).map q).hom w := by
      change z = _ + ((H.degree n).map s'.second).hom w
      rw [hw]; abel
    have e1 : (phi0.app Q).hom (((H.degree n).map beta).hom y) =
        ((K.degree n).map beta).hom ((phi0.app (R.U.obj s.A)).hom y) :=
      congrArg (fun f => f.hom y) (phi0.naturality beta)
    have e2 : (phi0.app Q).hom (((H.degree n).map q).hom w) =
        ((K.degree n).map q).hom ((phi0.app (R.I.obj s.B)).hom w) :=
      congrArg (fun f => f.hom w) (phi0.naturality q)
    have e3 : (K.connecting s' n).hom (((K.degree n).map q).hom ((phi0.app (R.I.obj s.B)).hom w)) = 0 :=
      (K.exact_right s' n _).2 ⟨_, rfl⟩
    have e4 : (phi1.app s.A).hom ((H.connecting (R.sequence s.A) n).hom y) =
        (K.connecting (R.sequence s.A) n).hom ((phi0.app (R.U.obj s.A)).hom y) :=
      congrArg (fun f => f.hom y) (hsq s.A)
    rw [← hy, e4, ← nat1 K, hzw, map_add, map_add, e1, e2, e3, add_zero]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  change (phi1.app s.A).hom ((H.connecting s n).hom x) = (K.connecting s n).hom ((phi0.app s.D).hom x)
  have e5 : (phi0.app Q).hom (((H.degree n).map gamma).hom x) =
      ((K.degree n).map gamma).hom ((phi0.app s.D).hom x) :=
    congrArg (fun f => f.hom x) (phi0.naturality gamma)
  rw [← nat2 H, main, e5, nat2 K]

theorem g66e_unique (R : FunctorialResolution S) (H K : DeltaFunctor.{u, v, w} S)
    (hz : ∀ A n, 1 ≤ n → Limits.IsZero ((H.degree n).obj (R.I.obj A)))
    (phi psi : DegreeFamily H K) (h0 : phi.component 0 = psi.component 0)
    (hphi : ∀ A n, CommutesConnecting phi (R.sequence A) n)
    (hpsi : ∀ A n, CommutesConnecting psi (R.sequence A) n) : phi = psi := by
  have key : ∀ n, phi.component n = psi.component n := by
    intro n
    induction n with
    | zero => exact h0
    | succ n ih =>
      apply g66e_step_unique R H K n (phi.component n) (fun A => hz A (n+1) (by omega))
      · intro A; exact hphi A n
      · intro A; rw [ih]; exact hpsi A n
  cases phi; cases psi
  congr
  funext n
  exact key n

theorem g66e_bij {X Y : DeltaFunctor.{u, v, w} S} (phi : DegreeFamily X Y)
    (R1 R2 : FunctorialResolution S)
    (hY : ∀ A n, 1 ≤ n → Limits.IsZero ((Y.degree n).obj (R1.I.obj A)))
    (hX : ∀ A n, 1 ≤ n → Limits.IsZero ((X.degree n).obj (R2.I.obj A)))
    (h1 : ∀ A n, CommutesConnecting phi (R1.sequence A) n)
    (h2 : ∀ A n, CommutesConnecting phi (R2.sequence A) n)
    (h0 : ∀ A, Function.Bijective ((phi.component 0).app A).hom) :
    ∀ n A, Function.Bijective ((phi.component n).app A).hom := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih =>
    intro A
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ := g66e_surj2 R2 X A n (hX A (n+1) (by omega)) x
      have e : ((phi.component (n+1)).app A).hom ((X.connecting (R2.sequence A) n).hom y) =
          (Y.connecting (R2.sequence A) n).hom (((phi.component n).app (R2.U.obj A)).hom y) :=
        congrArg (fun g => g.hom y) (h2 A n)
      rw [e] at hx
      obtain ⟨w, hw⟩ := (Y.exact_right (R2.sequence A) n _).1 hx
      obtain ⟨w', rfl⟩ := (ih (R2.I.obj A)).2 w
      have hn : ((phi.component n).app (R2.U.obj A)).hom (((X.degree n).map (R2.zeta.app A)).hom w') =
          ((Y.degree n).map (R2.zeta.app A)).hom (((phi.component n).app (R2.I.obj A)).hom w') :=
        congrArg (fun g => g.hom w') ((phi.component n).naturality (R2.zeta.app A))
      have hy : y = ((X.degree n).map (R2.zeta.app A)).hom w' := by
        apply (ih (R2.U.obj A)).1
        rw [hn]; exact hw.symm
      rw [hy]
      exact (X.exact_right (R2.sequence A) n _).2 ⟨_, rfl⟩
    · intro yv
      obtain ⟨z, rfl⟩ := g66e_surj2 R1 Y A n (hY A (n+1) (by omega)) yv
      obtain ⟨z', rfl⟩ := (ih (R1.U.obj A)).2 z
      exact ⟨(X.connecting (R1.sequence A) n).hom z', congrArg (fun g => g.hom z') (h1 A n)⟩

theorem g66e_isIso_of_bij {F G : C ⥤ AddCommGrpCat.{w}} (phi : F ⟶ G)
    (h : ∀ A, Function.Bijective (phi.app A).hom) : IsIso phi := by
  haveI : ∀ A, IsIso (phi.app A) := fun A => (ConcreteCategory.isIso_iff_bijective _).2 (h A)
  exact NatIso.isIso_of_isIso_app _

theorem g66e_bij_of_isIso {F G : C ⥤ AddCommGrpCat.{w}} (phi : F ⟶ G) [IsIso phi] (A : C) :
    Function.Bijective (phi.app A).hom :=
  (ConcreteCategory.isIso_iff_bijective _).1 inferInstance

def g66e_dm (R : FunctorialResolution S) (H K : DeltaFunctor.{u, v, w} S)
    (hq : CompatibleQuotients R)
    (hz : ∀ A n, 1 ≤ n → Limits.IsZero ((H.degree n).obj (R.I.obj A)))
    (alpha : H.degree 0 ⟶ K.degree 0) : DeltaMorphism H K where
  component := g66e_fam R H K alpha
  commutes := fun s n => g66e_allseq R H K n _ _
    (g66e_fam_sq R H K alpha n (fun A => hz A (n+1) (by omega)))
    (fun A => hz A (n+1) (by omega)) hq s

def g66e_inv {X Y : DeltaFunctor.{u, v, w} S} (phi : DeltaMorphism X Y)
    (h : ∀ n, IsIso (phi.component n)) : DeltaMorphism Y X where
  component := fun n => inv (phi.component n)
  commutes := by
    intro s n
    change Y.connecting s n ≫ (inv (phi.component (n+1))).app s.A =
      (inv (phi.component n)).app s.D ≫ X.connecting s n
    rw [NatIso.isIso_inv_app, NatIso.isIso_inv_app, IsIso.eq_inv_comp, ← Category.assoc,
      IsIso.comp_inv_eq]
    exact (phi.commutes s n).symm

end

theorem solution
    {C : Type u} [Category.{v} C] (S : SequenceClass C)
    (R Rprime : FunctorialResolution S) (H K : DeltaFunctor.{u, v, w} S)
    (hH : ∀ (A : C) (n : ℕ), 1 ≤ n →
      Limits.IsZero ((H.degree n).obj (R.I.obj A)))
    (hK : ∀ (A : C) (n : ℕ), 1 ≤ n →
      Limits.IsZero ((K.degree n).obj (Rprime.I.obj A)))
    (hquot : CompatibleQuotients R ∨ CompatibleQuotients Rprime)
    (alpha : H.degree 0 ≅ K.degree 0) :
    ∃ e : DeltaEquivalence H K,
      e.forward.component 0 = alpha.hom ∧
      e.backward.component 0 = alpha.inv ∧
      (∀ phi : DegreeFamily H K,
        ResolutionExtension R alpha.hom phi → phi = e.forward.toDegreeFamily) ∧
      (∀ psi : DegreeFamily K H,
        ResolutionExtension Rprime alpha.inv psi → psi = e.backward.toDegreeFamily) := by
  rcases hquot with hq | hq
  · let phi := g66e_dm R H K hq hH alpha.hom
    have hiso : ∀ n, IsIso (phi.component n) := fun n =>
      g66e_isIso_of_bij _ (g66e_bij phi.toDegreeFamily Rprime R hK hH
        (fun A n => phi.commutes _ n) (fun A n => phi.commutes _ n)
        (fun A => g66e_bij_of_isIso alpha.hom A) n)
    refine ⟨⟨phi, g66e_inv phi hiso, fun n => IsIso.hom_inv_id _,
      fun n => IsIso.inv_hom_id _⟩, rfl, ?_, ?_, ?_⟩
    · change inv alpha.hom = alpha.inv
      simp
    · intro phi' h
      exact g66e_unique R H K hH phi' _ h.1 h.2 (fun A n => phi.commutes _ n)
    · intro psi' h
      refine g66e_unique Rprime K H hK psi' _ ?_ h.2
        (fun A n => (g66e_inv phi hiso).commutes _ n)
      rw [h.1]
      change alpha.inv = inv alpha.hom
      simp
  · let psi := g66e_dm Rprime K H hq hK alpha.inv
    have hiso : ∀ n, IsIso (psi.component n) := fun n =>
      g66e_isIso_of_bij _ (g66e_bij psi.toDegreeFamily R Rprime hH hK
        (fun A n => psi.commutes _ n) (fun A n => psi.commutes _ n)
        (fun A => g66e_bij_of_isIso alpha.inv A) n)
    refine ⟨⟨g66e_inv psi hiso, psi, fun n => IsIso.inv_hom_id _,
      fun n => IsIso.hom_inv_id _⟩, ?_, rfl, ?_, ?_⟩
    · change inv alpha.inv = alpha.hom
      simp
    · intro phi' h
      refine g66e_unique R H K hH phi' _ ?_ h.2
        (fun A n => (g66e_inv psi hiso).commutes _ n)
      rw [h.1]
      change alpha.hom = inv alpha.inv
      simp
    · intro psi' h
      exact g66e_unique Rprime K H hK psi' _ h.1 h.2 (fun A n => psi.commutes _ n)
