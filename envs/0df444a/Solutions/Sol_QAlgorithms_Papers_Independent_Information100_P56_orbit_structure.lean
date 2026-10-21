-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P56.orbit_structure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:59:06.116459+00:00
-- url     : https://prove2.me/submissions/2d032370-d638-47fa-ab2a-f9dc6acaa92c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

def h54b_push {α β : Type*} [Fintype α] (φ : α → β) (Q : α → ℝ) (b : β) : ℝ :=
  ∑ a, if φ a = b then Q a else 0

lemma h54b_push_sum {α β : Type*} [Fintype α] [Fintype β] (φ : α → β) (Q : α → ℝ) :
    ∑ b, h54b_push φ Q b = ∑ a, Q a := by
  unfold h54b_push
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp

lemma h54b_push_law {α β : Type*} [Fintype α] [Fintype β] (φ : α → β) (Q : α → ℝ)
    (hQ : IsLaw Q) : IsLaw (h54b_push φ Q) := by
  refine ⟨fun b => Finset.sum_nonneg (fun a _ => ?_), by rw [h54b_push_sum, hQ.2]⟩
  split_ifs
  · exact hQ.1 a
  · exact le_refl _

lemma h54b_push_smul {α β : Type*} [Fintype α] [Fintype β] {K : Type*} [AddCommMonoid K]
    [Module ℂ K] (φ : α → β) (Q : α → ℝ) (F : β → K) :
    ∑ b, ((h54b_push φ Q b : ℝ) : ℂ) • F b = ∑ a, ((Q a : ℝ) : ℂ) • F (φ a) := by
  unfold h54b_push
  simp only [Complex.ofReal_sum, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single (φ a)]
  · simp
  · intro b _ hb
    rw [if_neg (Ne.symm hb)]; simp
  · simp

lemma h54b_push_push {α β γ : Type*} [Fintype α] [Fintype β] (φ : β → γ) (ψ : α → β)
    (Q : α → ℝ) : h54b_push φ (h54b_push ψ Q) = h54b_push (φ ∘ ψ) Q := by
  funext c
  unfold h54b_push
  simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  rw [Finset.sum_comm' (t' := Finset.univ.filter (fun a => φ (ψ a) = c))
    (s' := fun a => Finset.univ.filter (fun b => φ b = c ∧ ψ a = b))]
  · refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    rw [Finset.sum_const, Finset.card_eq_one.mpr ⟨ψ a, ?_⟩]
    · simp
    · ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩; exact h.symm
      · rintro rfl; exact ⟨ha.2, rfl⟩
  · intro b a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, rfl⟩; exact ⟨⟨h1, rfl⟩, h1⟩
    · rintro ⟨h, -⟩; exact h

lemma h54b_push_id {α : Type*} [Fintype α] (φ : α → α) (hφ : ∀ a, φ a = a) (Q : α → ℝ) :
    h54b_push φ Q = Q := by
  funext b
  unfold h54b_push
  simp [hφ]

lemma h54b_orbit_mul {G B : Type*} [Group G] [Fintype B] [DecidableEq B]
    (U : ProjectiveRep G B) (ρ : Matrix B B ℂ) (v y : G) :
    orbit U ρ (v * y) = (U.unitary v : Matrix B B ℂ) * orbit U ρ y * (U.unitary v : Matrix B B ℂ)ᴴ := by
  unfold orbit
  rw [U.mul_phase]
  have hp : U.phase v y * star (U.phase v y) = 1 := by
    have := U.phase_norm v y
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, this]
    simp
  rw [Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm, hp, one_smul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

lemma h54b_orbit_density {G B : Type*} [Group G] [Fintype B] [DecidableEq B]
    (U : ProjectiveRep G B) (ρ : Matrix B B ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ) (g : G) :
    QAlgorithms.IsDensityMatrix (orbit U ρ g) := by
  unfold orbit
  refine ⟨hρ.1.mul_mul_conjTranspose_same _, ?_⟩
  rw [Matrix.trace_mul_cycle]
  have hu : (U.unitary g : Matrix B B ℂ)ᴴ * (U.unitary g : Matrix B B ℂ) = 1 :=
    Unitary.star_mul_self_of_mem (U.unitary g).2
  rw [hu, Matrix.one_mul, hρ.2]

lemma h54b_pj {V α β : Type*} [Fintype α] [DecidableEq β] (φ : α → β) (J : V × α → ℝ) (v : V)
    (y : β) : pushJoint φ J (v, y) = h54b_push φ (fun g => J (v, g)) y := by
  unfold pushJoint h54b_push
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  congr

lemma h54b_pj_law {V α β : Type*} [Fintype V] [Fintype α] [Fintype β] [DecidableEq β]
    (φ : α → β) (J : V × α → ℝ) (hJ : IsLaw J) : IsLaw (pushJoint φ J) := by
  refine ⟨fun vy => ?_, ?_⟩
  · obtain ⟨v, y⟩ := vy
    rw [h54b_pj]
    unfold h54b_push
    exact Finset.sum_nonneg (fun g _ => by split_ifs; exacts [hJ.1 _, le_refl _])
  · rw [Fintype.sum_prod_type]
    simp only [h54b_pj, h54b_push_sum]
    rw [← Fintype.sum_prod_type]
    exact hJ.2

lemma h54b_block_eq {G X B E : Type*} [Fintype G] [Fintype X] [Fintype B] [DecidableEq B]
    [Fintype E] [DecidableEq E] (n : ℕ) (act : G → X) (sec : X → G) (hs : ∀ x, act (sec x) = x)
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) :
    blockPrivate n WB WE = blockPrivate n (fun g => WB (act g)) (fun g => WE (act g)) := by
  unfold blockPrivate privateInfo
  congr 1
  let f : (Fin n → G) → (Fin n → X) := fun g i => act (g i)
  let sc : (Fin n → X) → (Fin n → G) := fun y i => sec (y i)
  have hfs : ∀ y, f (sc y) = y := by intro y; funext i; simp [f, sc, hs]
  have avgB : ∀ Q : (Fin n → G) → ℝ, average (productOutput n WB) (h54b_push f Q) =
      average (productOutput n (fun g => WB (act g))) Q := by
    intro Q; unfold average; rw [h54b_push_smul]; rfl
  have avgE : ∀ Q : (Fin n → G) → ℝ, average (productOutput n WE) (h54b_push f Q) =
      average (productOutput n (fun g => WE (act g))) Q := by
    intro Q; unfold average; rw [h54b_push_smul]; rfl
  have avgB' : ∀ Q : (Fin n → X) → ℝ,
      average (productOutput n (fun g => WB (act g))) (h54b_push sc Q) =
      average (productOutput n WB) Q := by
    intro Q; unfold average; rw [h54b_push_smul]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    show _ • productOutput n WB (f (sc y)) = _
    rw [hfs]
  have avgE' : ∀ Q : (Fin n → X) → ℝ,
      average (productOutput n (fun g => WE (act g))) (h54b_push sc Q) =
      average (productOutput n WE) Q := by
    intro Q; unfold average; rw [h54b_push_smul]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    show _ • productOutput n WE (f (sc y)) = _
    rw [hfs]
  ext r
  constructor
  · rintro ⟨A, rfl⟩
    refine ⟨⟨A.size, A.positive, A.outer, A.outer_law, fun v => h54b_push sc (A.conditional v),
      fun v => h54b_push_law _ _ (A.conditional_law v)⟩, ?_⟩
    unfold encoderValue
    simp only [avgB', avgE']
  · rintro ⟨A, rfl⟩
    refine ⟨⟨A.size, A.positive, A.outer, A.outer_law, fun v => h54b_push f (A.conditional v),
      fun v => h54b_push_law _ _ (A.conditional_law v)⟩, ?_⟩
    unfold encoderValue
    simp only [avgB, avgE]

theorem solution
    {G X B E : Type*} [Group G] [Fintype G] [Fintype X] [DecidableEq X]
    [MulAction G X] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (x0 : X) (htrans : ∀ x : X, ∃ g : G, g • x0 = x)
    (UB : ProjectiveRep G B) (UE : ProjectiveRep G E)
    (WB : X → Matrix B B ℂ) (WE : X → Matrix E E ℂ) (hW : IsWiretap WB WE)
    (hcovB : ∀ g x, WB (g • x) =
      (UB.unitary g : Matrix B B ℂ) * WB x * (UB.unitary g : Matrix B B ℂ)ᴴ)
    (hcovE : ∀ g x, WE (g • x) =
      (UE.unitary g : Matrix E E ℂ) * WE x * (UE.unitary g : Matrix E E ℂ)ᴴ) :
    (∃ e : Quotient (actionRelation x0) ≃ X,
      ∀ g : G, e (Quotient.mk (actionRelation x0) g) = g • x0) ∧
    (∀ g h : G, (actionRelation x0).r g h ↔ (g⁻¹ * h) • x0 = x0) ∧
    (∀ g, WB (g • x0) = orbit UB (WB x0) g ∧ WE (g • x0) = orbit UE (WE x0) g) ∧
    (∀ h : G, h • x0 = x0 → orbit UB (WB x0) h = WB x0 ∧ orbit UE (WE x0) h = WE x0) ∧
    (∀ (sigmaB : Matrix B B ℂ) (sigmaE : Matrix E E ℂ),
      QAlgorithms.IsDensityMatrix sigmaB → QAlgorithms.IsDensityMatrix sigmaE →
      (∀ h : G, h • x0 = x0 → orbit UB sigmaB h = sigmaB ∧ orbit UE sigmaE h = sigmaE) →
      ∃ (YB : X → Matrix B B ℂ) (YE : X → Matrix E E ℂ), IsWiretap YB YE ∧
        (∀ g, YB (g • x0) = orbit UB sigmaB g ∧ YE (g • x0) = orbit UE sigmaE g) ∧
        (∀ g x, YB (g • x) = orbit UB (YB x) g ∧ YE (g • x) = orbit UE (YE x) g)) ∧
    (∀ n : ℕ, 1 ≤ n →
      blockPrivate n WB WE = blockPrivate n (fun g : G => WB (g • x0)) (fun g : G => WE (g • x0))) ∧
    (∀ (n k : ℕ), 1 ≤ n → 0 < k →
      let f : (Fin n → G) → (Fin n → X) := fun g i => g i • x0
      (∀ J : Fin k × (Fin n → X) → ℝ, IsLaw J →
        ∃ JG : Fin k × (Fin n → G) → ℝ, IsLaw JG ∧ pushJoint f JG = J) ∧
      (∀ JG : Fin k × (Fin n → G) → ℝ, IsLaw JG →
        IsLaw (pushJoint f JG) ∧ ∀ v : Fin k,
          cqBlock (productOutput n (fun g : G => WB (g • x0))) JG v =
            cqBlock (productOutput n WB) (pushJoint f JG) v ∧
          cqBlock (productOutput n (fun g : G => WE (g • x0))) JG v =
            cqBlock (productOutput n WE) (pushJoint f JG) v)) := by
  choose sec hsec using htrans
  have hrel : ∀ g h : G, g • x0 = h • x0 ↔ (g⁻¹ * h) • x0 = x0 := by
    intro g h
    rw [mul_smul, inv_smul_eq_iff]
    exact eq_comm
  refine ⟨?_, fun g h => hrel g h, fun g => ⟨hcovB g x0, hcovE g x0⟩,
    fun h hh => ⟨by unfold orbit; rw [← hcovB, hh],
      by unfold orbit; rw [← hcovE, hh]⟩, ?_, ?_, ?_⟩
  · let F : Quotient (actionRelation x0) → X :=
      Quotient.lift (fun g : G => g • x0) (fun a b h => h)
    have hF : Function.Bijective F := by
      constructor
      · intro p q hpq
        induction p using Quotient.ind
        induction q using Quotient.ind
        exact Quotient.sound hpq
      · intro x
        exact ⟨Quotient.mk _ (sec x), hsec x⟩
    exact ⟨Equiv.ofBijective F hF, fun g => rfl⟩
  · intro sB sE hsB hsE hstab
    -- well-definedness
    have wdB : ∀ g, orbit UB sB g = orbit UB sB (sec (g • x0)) := by
      intro g
      have hh : ((sec (g • x0))⁻¹ * g) • x0 = x0 := (hrel _ _).mp (hsec _)
      have : g = sec (g • x0) * ((sec (g • x0))⁻¹ * g) := by group
      rw [this, h54b_orbit_mul, (hstab _ hh).1, ← this]
      rfl
    have wdE : ∀ g, orbit UE sE g = orbit UE sE (sec (g • x0)) := by
      intro g
      have hh : ((sec (g • x0))⁻¹ * g) • x0 = x0 := (hrel _ _).mp (hsec _)
      have : g = sec (g • x0) * ((sec (g • x0))⁻¹ * g) := by group
      rw [this, h54b_orbit_mul, (hstab _ hh).2, ← this]
      rfl
    refine ⟨fun x => orbit UB sB (sec x), fun x => orbit UE sE (sec x),
      ⟨fun x => h54b_orbit_density _ _ hsB _, fun x => h54b_orbit_density _ _ hsE _⟩,
      fun g => ⟨(wdB g).symm, (wdE g).symm⟩, fun g x => ?_⟩
    have e : g • x = (g * sec x) • x0 := by rw [mul_smul, hsec]
    constructor
    · show orbit UB sB (sec (g • x)) = orbit UB (orbit UB sB (sec x)) g
      rw [e, ← wdB, h54b_orbit_mul]; rfl
    · show orbit UE sE (sec (g • x)) = orbit UE (orbit UE sE (sec x)) g
      rw [e, ← wdE, h54b_orbit_mul]; rfl
  · intro n _
    exact h54b_block_eq n (fun g : G => g • x0) sec hsec WB WE
  · intro n k _ _ f
    let sc : (Fin n → X) → (Fin n → G) := fun y i => sec (y i)
    have hfs : ∀ y, f (sc y) = y := by intro y; funext i; simp [f, sc, hsec]
    refine ⟨fun J hJ => ?_, fun JG hJ => ⟨h54b_pj_law f JG hJ, fun v => ⟨?_, ?_⟩⟩⟩
    · refine ⟨pushJoint sc J, h54b_pj_law sc J hJ, ?_⟩
      funext vy
      obtain ⟨v, y⟩ := vy
      rw [h54b_pj]
      have : (fun g => pushJoint sc J (v, g)) = h54b_push sc (fun y => J (v, y)) := by
        funext g; exact h54b_pj sc J v g
      rw [this, h54b_push_push, h54b_push_id (f ∘ sc) hfs]
    · unfold cqBlock
      simp only [h54b_pj]
      rw [h54b_push_smul]
      rfl
    · unfold cqBlock
      simp only [h54b_pj]
      rw [h54b_push_smul]
      rfl

end
