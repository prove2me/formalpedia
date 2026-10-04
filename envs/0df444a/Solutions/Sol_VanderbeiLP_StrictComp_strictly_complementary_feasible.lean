-- Prove2me | solution 1 for VanderbeiLP.StrictComp.strictly_complementary_feasible
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-03T18:50:24.021481+00:00
-- url     : https://prove2.me/submissions/8c360159-677d-43d2-bc0c-e8a41ce2fc9d

import Mathlib
import Definitions.Def_VanderbeiLP_StrictComp_PrimalDualPair
import Theorems.Thm_VanderbeiLP_StrictComp_strong_duality

open Matrix

-- Shared checked module: StrictCompGeometry

namespace VanderbeiLP.StrictComp
open Matrix Set
noncomputable section

lemma sc_primalSlack_combo {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x z : Fin n → ℝ) (a d : ℝ) (had : a+d=1) :
    primalSlack A b (a • x+d • z)=a • primalSlack A b x+d • primalSlack A b z := by
  ext i
  simp only [primalSlack,mulVec_add,mulVec_smul,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  nlinarith [congrArg (fun t : ℝ => t*b i) had]

lemma sc_dualSlack_combo {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (y z : Fin m → ℝ) (a d : ℝ) (had : a+d=1) :
    dualSlack A c (a • y+d • z)=a • dualSlack A c y+d • dualSlack A c z := by
  ext j
  simp only [dualSlack,mulVec_add,mulVec_smul,Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  nlinarith [congrArg (fun t : ℝ => t*c j) had]

lemma sc_primal_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ {x | PrimalFeasible A b x} := by
  intro x hx z hz a d ha hd had
  refine ⟨fun j => ?_,fun i => ?_⟩
  · change 0 ≤ a*x j+d*z j
    exact add_nonneg (mul_nonneg ha (hx.1 j)) (mul_nonneg hd (hz.1 j))
  · rw [sc_primalSlack_combo A b x z a d had]
    change 0 ≤ a*primalSlack A b x i+d*primalSlack A b z i
    exact add_nonneg (mul_nonneg ha (hx.2 i)) (mul_nonneg hd (hz.2 i))

lemma sc_dual_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    Convex ℝ {y | DualFeasible A c y} := by
  intro y hy z hz a d ha hd had
  refine ⟨fun i => ?_,fun j => ?_⟩
  · change 0 ≤ a*y i+d*z i
    exact add_nonneg (mul_nonneg ha (hy.1 i)) (mul_nonneg hd (hz.1 i))
  · rw [sc_dualSlack_combo A c y z a d had]
    change 0 ≤ a*dualSlack A c y j+d*dualSlack A c z j
    exact add_nonneg (mul_nonneg ha (hy.2 j)) (mul_nonneg hd (hz.2 j))

-- Midpoint averaging turns separate positive-coordinate witnesses into one simultaneous witness.
lemma sc_finite_positive {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (S : Set E) (hS : Convex ℝ S) (hne : S.Nonempty) (q : ι → E → ℝ)
    (hq0 : ∀ i, ∀ x ∈ S, 0 ≤ q i x)
    (hqmid : ∀ i x z, q i ((1/2:ℝ) • x+(1/2:ℝ) • z)=(q i x+q i z)/2)
    (hq : ∀ i, ∃ x ∈ S, 0 < q i x) :
    ∃ x ∈ S, ∀ i, 0 < q i x := by
  classical
  have aux : ∀ s : Finset ι, ∃ x ∈ S, ∀ i ∈ s, 0 < q i x := by
    intro s
    induction s using Finset.induction_on with
    | empty => obtain ⟨x,hx⟩ := hne; exact ⟨x,hx,by simp⟩
    | @insert i s hi ih =>
      obtain ⟨x,hx,hpos⟩ := ih
      obtain ⟨z,hz,hzpos⟩ := hq i
      refine ⟨(1/2:ℝ) • x+(1/2:ℝ) • z,
        hS hx hz (by norm_num) (by norm_num) (by norm_num),?_⟩
      intro j hj
      rw [hqmid]
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · linarith [hq0 j x hx]
      · linarith [hpos j hjs,hq0 j z hz]
  obtain ⟨x,hx,hs⟩ := aux Finset.univ
  exact ⟨x,hx,fun i => hs i (Finset.mem_univ i)⟩

def sc_optimalPairs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (v : ℝ) : Set ((Fin n → ℝ) × (Fin m → ℝ)) :=
  {p | PrimalFeasible A b p.1 ∧ DualFeasible A c p.2 ∧ c ⬝ᵥ p.1=v ∧ b ⬝ᵥ p.2=v}

lemma sc_optimalPairs_convex {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (v : ℝ) : Convex ℝ (sc_optimalPairs A b c v) := by
  intro x hx z hz a d ha hd had
  refine ⟨sc_primal_convex A b hx.1 hz.1 ha hd had,
    sc_dual_convex A c hx.2.1 hz.2.1 ha hd had,?_,?_⟩
  · change c ⬝ᵥ (a • x.1+d • z.1)=v
    rw [dotProduct_add,dotProduct_smul,dotProduct_smul,smul_eq_mul,smul_eq_mul,hx.2.2.1,hz.2.2.1]
    nlinarith [congrArg (fun t : ℝ => t*v) had]
  · change b ⬝ᵥ (a • x.2+d • z.2)=v
    rw [dotProduct_add,dotProduct_smul,dotProduct_smul,smul_eq_mul,smul_eq_mul,hx.2.2.2,hz.2.2.2]
    nlinarith [congrArg (fun t : ℝ => t*v) had]

def sc_compCoord {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (j : Fin n ⊕ Fin m) (p : (Fin n → ℝ) × (Fin m → ℝ)) : ℝ :=
  Sum.elim (fun j => p.1 j+dualSlack A c p.2 j)
    (fun i => p.2 i+primalSlack A b p.1 i) j

lemma sc_compCoord_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (v : ℝ) (j : Fin n ⊕ Fin m)
    (p : (Fin n → ℝ) × (Fin m → ℝ)) (hp : p ∈ sc_optimalPairs A b c v) :
    0 ≤ sc_compCoord A b c j p := by
  cases j with
  | inl j => exact add_nonneg (hp.1.1 j) (hp.2.1.2 j)
  | inr i => exact add_nonneg (hp.2.1.1 i) (hp.1.2 i)

lemma sc_compCoord_midpoint {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (j : Fin n ⊕ Fin m)
    (p z : (Fin n → ℝ) × (Fin m → ℝ)) :
    sc_compCoord A b c j ((1/2:ℝ) • p+(1/2:ℝ) • z)=
      (sc_compCoord A b c j p+sc_compCoord A b c j z)/2 := by
  cases j with
  | inl j =>
    change ((1/2:ℝ) • p.1+(1/2:ℝ) • z.1) j+
      dualSlack A c ((1/2:ℝ) • p.2+(1/2:ℝ) • z.2) j=_
    rw [sc_dualSlack_combo A c p.2 z.2 (1/2) (1/2) (by norm_num)]
    simp only [sc_compCoord,Sum.elim_inl,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  | inr i =>
    change ((1/2:ℝ) • p.2+(1/2:ℝ) • z.2) i+
      primalSlack A b ((1/2:ℝ) • p.1+(1/2:ℝ) • z.1) i=_
    rw [sc_primalSlack_combo A b p.1 z.1 (1/2) (1/2) (by norm_num)]
    simp only [sc_compCoord,Sum.elim_inr,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring

end
end VanderbeiLP.StrictComp

-- Shared checked module: StrictCompFace

namespace VanderbeiLP.StrictComp
open Matrix Set
noncomputable section

def sc_faceA {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    Matrix (Fin (m+1)) (Fin n) ℝ := Fin.snoc (α := fun _ => Fin n → ℝ) (fun i => A i) (-c)
def sc_faceB {m : ℕ} (b : Fin m → ℝ) (v : ℝ) : Fin (m+1) → ℝ := Fin.snoc (α := fun _ => ℝ) b (-v)

lemma sc_face_cast_slack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c x : Fin n → ℝ) (v : ℝ) (i : Fin m) :
    primalSlack (sc_faceA A c) (sc_faceB b v) x i.castSucc=primalSlack A b x i := by
  change Fin.snoc (α := fun _ => ℝ) b (-v) i.castSucc-(Fin.snoc (α := fun _ => Fin n → ℝ) (fun i => A i) (-c) i.castSucc) ⬝ᵥ x=
    b i-(A i) ⬝ᵥ x
  rw [Fin.snoc_castSucc,Fin.snoc_castSucc]

lemma sc_face_last_slack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c x : Fin n → ℝ) (v : ℝ) :
    primalSlack (sc_faceA A c) (sc_faceB b v) x (Fin.last m)=c ⬝ᵥ x-v := by
  change Fin.snoc (α := fun _ => ℝ) b (-v) (Fin.last m)-(Fin.snoc (α := fun _ => Fin n → ℝ) (fun i => A i) (-c) (Fin.last m)) ⬝ᵥ x=c ⬝ᵥ x-v
  rw [Fin.snoc_last,Fin.snoc_last,neg_dotProduct]
  ring

lemma sc_face_feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c x : Fin n → ℝ) (v : ℝ) :
    PrimalFeasible (sc_faceA A c) (sc_faceB b v) x ↔ PrimalFeasible A b x ∧ v ≤ c ⬝ᵥ x := by
  constructor
  · intro hx
    refine ⟨⟨hx.1,fun i => ?_⟩,?_⟩
    · simpa [sc_face_cast_slack] using hx.2 i.castSucc
    · have h := hx.2 (Fin.last m)
      rw [sc_face_last_slack] at h
      linarith
  · rintro ⟨hx,hv⟩
    refine ⟨hx.1,fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [sc_face_last_slack]; linarith
    · rw [sc_face_cast_slack]; exact hx.2 j

lemma sc_face_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (y : Fin (m+1) → ℝ) :
    (sc_faceA A c)ᵀ *ᵥ y=Aᵀ *ᵥ (fun i => y i.castSucc)-y (Fin.last m) • c := by
  ext j
  change (∑ i : Fin (m+1), Fin.snoc (α := fun _ => Fin n → ℝ) (fun i => A i) (-c) i j*y i)=
    (∑ i : Fin m, A i j*y i.castSucc)-y (Fin.last m)*c j
  rw [Fin.sum_univ_castSucc]
  have hc : ∀ i : Fin m, Fin.snoc (α := fun _ => Fin n → ℝ) (fun i => A i) (-c) i.castSucc j=A i j := by
    intro i
    exact congrFun (Fin.snoc_castSucc (α := fun _ => Fin n → ℝ) (-c) (fun i => A i) i) j
  have hl : Fin.snoc (α := fun _ => Fin n → ℝ) (fun i => A i) (-c) (Fin.last m) j= -c j := by
    exact congrFun (Fin.snoc_last (α := fun _ => Fin n → ℝ) (-c) (fun i => A i)) j
  simp only [hc,hl]
  ring

lemma sc_face_objective {m : ℕ} (b : Fin m → ℝ) (v : ℝ) (y : Fin (m+1) → ℝ) :
    sc_faceB b v ⬝ᵥ y=b ⬝ᵥ (fun i => y i.castSucc)-y (Fin.last m)*v := by
  simp only [dotProduct,Fin.sum_univ_castSucc,sc_faceB,Fin.snoc_castSucc,Fin.snoc_last]
  ring

-- Strong duality on the optimal face gives an exact certificate for a forced-zero coordinate.
lemma sc_face_certificate {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c x₀ ℓ : Fin n → ℝ) (hx₀ : PrimalOptimal A b c x₀)
    (hℓ : ∀ x, PrimalOptimal A b c x → ℓ ⬝ᵥ x ≤ ℓ ⬝ᵥ x₀) :
    ∃ (u : Fin m → ℝ) (σ : ℝ), (∀ i, 0 ≤ u i) ∧ 0 ≤ σ ∧
      (∀ j, ℓ j ≤ (Aᵀ *ᵥ u) j-σ*c j) ∧
      b ⬝ᵥ u-σ*(c ⬝ᵥ x₀)=ℓ ⬝ᵥ x₀ := by
  let v := c ⬝ᵥ x₀
  have hxface : PrimalOptimal (sc_faceA A c) (sc_faceB b v) ℓ x₀ := by
    refine ⟨(sc_face_feasible A b c x₀ v).mpr ⟨hx₀.1,le_rfl⟩,?_⟩
    intro x hx
    obtain ⟨hx,hv⟩ := (sc_face_feasible A b c x v).mp hx
    exact hℓ x ⟨hx,fun z hz => (hx₀.2 z hz).trans hv⟩
  obtain ⟨y,hy,he⟩ := strong_duality (sc_faceA A c) (sc_faceB b v) ℓ x₀ hxface
  refine ⟨fun i => y i.castSucc,y (Fin.last m),fun i => hy.1.1 _,hy.1.1 _,?_,?_⟩
  · intro j
    have h := hy.1.2 j
    change 0 ≤ ((sc_faceA A c)ᵀ *ᵥ y) j-ℓ j at h
    rw [sc_face_transpose] at h
    change 0 ≤ (Aᵀ *ᵥ (fun i => y i.castSucc)) j-y (Fin.last m)*c j-ℓ j at h
    linarith
  · rw [sc_face_objective] at he
    exact he.symm

def sc_lift {m : ℕ} (y u : Fin m → ℝ) (σ : ℝ) : Fin m → ℝ :=
  (1/(σ+1)) • (y+u)

lemma sc_lift_slack {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (y u : Fin m → ℝ) (σ : ℝ) (hσ : 0 ≤ σ) (j : Fin n) :
    dualSlack A c (sc_lift y u σ) j=
      (dualSlack A c y j+(Aᵀ *ᵥ u) j-σ*c j)/(σ+1) := by
  have hn : σ+1 ≠ 0 := by linarith
  simp only [sc_lift,dualSlack,mulVec_smul,mulVec_add,Pi.sub_apply,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul]
  field_simp
  ring

lemma sc_lift_feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (y u : Fin m → ℝ) (σ : ℝ) (hσ : 0 ≤ σ)
    (hy : DualFeasible A c y) (hu : ∀ i, 0 ≤ u i)
    (hcert : ∀ j, 0 ≤ (Aᵀ *ᵥ u) j-σ*c j) :
    DualFeasible A c (sc_lift y u σ) := by
  refine ⟨fun i => ?_,fun j => ?_⟩
  · change 0 ≤ (1/(σ+1))*(y i+u i)
    exact mul_nonneg (by positivity) (add_nonneg (hy.1 i) (hu i))
  · rw [sc_lift_slack A c y u σ hσ]
    exact div_nonneg (by linarith [hy.2 j,hcert j]) (by linarith)

lemma sc_lift_value {m : ℕ} (b y u : Fin m → ℝ) (σ v : ℝ) (hσ : 0 ≤ σ)
    (hy : b ⬝ᵥ y=v) (hu : b ⬝ᵥ u-σ*v=0) : b ⬝ᵥ sc_lift y u σ=v := by
  have hn : σ+1 ≠ 0 := by linarith
  simp only [sc_lift,dotProduct_smul,dotProduct_add,smul_eq_mul,hy]
  field_simp
  nlinarith

lemma sc_transpose_single {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) :
    Aᵀ *ᵥ (Pi.single i (1:ℝ))=A i := by
  ext j
  simp [mulVec,transpose_apply]

end
end VanderbeiLP.StrictComp

-- Shared checked module: StrictCompCertificates

namespace VanderbeiLP.StrictComp
open Matrix Set
noncomputable section

lemma sc_variable_witness {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c x₀ : Fin n → ℝ) (hx₀ : PrimalOptimal A b c x₀)
    (y₀ : Fin m → ℝ) (hy₀ : DualFeasible A c y₀) (he₀ : b ⬝ᵥ y₀=c ⬝ᵥ x₀)
    (j : Fin n) (hzero : ∀ x, PrimalOptimal A b c x → x j=0) :
    ∃ y : Fin m → ℝ, DualFeasible A c y ∧ b ⬝ᵥ y=c ⬝ᵥ x₀ ∧ 0 < dualSlack A c y j := by
  let ℓ : Fin n → ℝ := Pi.single j 1
  have hℓ : ∀ x, PrimalOptimal A b c x → ℓ ⬝ᵥ x ≤ ℓ ⬝ᵥ x₀ := by
    intro x hx
    simp [ℓ,hzero x hx,hzero x₀ hx₀]
  obtain ⟨u,σ,hu,hσ,hcert,hval⟩ := sc_face_certificate A b c x₀ ℓ hx₀ hℓ
  have hval0 : b ⬝ᵥ u-σ*(c ⬝ᵥ x₀)=0 := by
    simpa [ℓ,single_one_dotProduct,hzero x₀ hx₀] using hval
  have hcert0 : ∀ k, 0 ≤ (Aᵀ *ᵥ u) k-σ*c k := by
    intro k
    have hn : 0 ≤ ℓ k := by dsimp [ℓ]; by_cases hk : k=j <;> simp [hk]
    exact hn.trans (hcert k)
  refine ⟨sc_lift y₀ u σ,sc_lift_feasible A c y₀ u σ hσ hy₀ hu hcert0,
    sc_lift_value b y₀ u σ (c ⬝ᵥ x₀) hσ he₀ hval0,?_⟩
  rw [sc_lift_slack A c y₀ u σ hσ]
  have hj : 1 ≤ (Aᵀ *ᵥ u) j-σ*c j := by simpa [ℓ] using hcert j
  exact div_pos (by linarith [hy₀.2 j]) (by linarith)

lemma sc_slack_witness {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c x₀ : Fin n → ℝ) (hx₀ : PrimalOptimal A b c x₀)
    (y₀ : Fin m → ℝ) (hy₀ : DualFeasible A c y₀) (he₀ : b ⬝ᵥ y₀=c ⬝ᵥ x₀)
    (i : Fin m) (hzero : ∀ x, PrimalOptimal A b c x → primalSlack A b x i=0) :
    ∃ y : Fin m → ℝ, DualFeasible A c y ∧ b ⬝ᵥ y=c ⬝ᵥ x₀ ∧ 0 < y i := by
  let ℓ : Fin n → ℝ := -A i
  have hℓvalue : ∀ x, PrimalOptimal A b c x → ℓ ⬝ᵥ x= -b i := by
    intro x hx
    have hs := hzero x hx
    change b i-(A *ᵥ x) i=0 at hs
    change (-A i) ⬝ᵥ x= -b i
    rw [neg_dotProduct]
    change -((A *ᵥ x) i)= -b i
    linarith
  have hℓ : ∀ x, PrimalOptimal A b c x → ℓ ⬝ᵥ x ≤ ℓ ⬝ᵥ x₀ := by
    intro x hx; rw [hℓvalue x hx,hℓvalue x₀ hx₀]
  obtain ⟨u,σ,hu,hσ,hcert,hval⟩ := sc_face_certificate A b c x₀ ℓ hx₀ hℓ
  let u' : Fin m → ℝ := u+Pi.single i 1
  have hu' : ∀ k, 0 ≤ u' k := by
    intro k
    change 0 ≤ u k+Pi.single (M := fun _ => ℝ) i (1:ℝ) k
    have hn : 0 ≤ Pi.single (M := fun _ => ℝ) i (1:ℝ) k := by by_cases hk : k=i <;> simp [hk]
    exact add_nonneg (hu k) hn
  have hAu' : Aᵀ *ᵥ u'=Aᵀ *ᵥ u+A i := by
    dsimp only [u']
    rw [mulVec_add,sc_transpose_single]
  have hcert0 : ∀ j, 0 ≤ (Aᵀ *ᵥ u') j-σ*c j := by
    intro j
    rw [hAu']
    have h := hcert j
    change -A i j ≤ (Aᵀ *ᵥ u) j-σ*c j at h
    change 0 ≤ (Aᵀ *ᵥ u) j+A i j-σ*c j
    linarith
  have hval0 : b ⬝ᵥ u'-σ*(c ⬝ᵥ x₀)=0 := by
    dsimp only [u']
    rw [dotProduct_add,dotProduct_single_one]
    rw [hℓvalue x₀ hx₀] at hval
    linarith
  refine ⟨sc_lift y₀ u' σ,sc_lift_feasible A c y₀ u' σ hσ hy₀ hu' hcert0,
    sc_lift_value b y₀ u' σ (c ⬝ᵥ x₀) hσ he₀ hval0,?_⟩
  change 0 < (1/(σ+1))*(y₀ i+u' i)
  have he : u' i=u i+1 := by simp [u']
  rw [he]
  exact mul_pos (by positivity) (by linarith [hy₀.1 i,hu i])

end
end VanderbeiLP.StrictComp

-- Shared checked module: StrictCompComplete

namespace VanderbeiLP.StrictComp
open Matrix Set
noncomputable section

lemma sc_primal_optimal_value {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ} {c x z : Fin n → ℝ}
    (hx : PrimalOptimal A b c x) (hz : PrimalOptimal A b c z) : c ⬝ᵥ x=c ⬝ᵥ z :=
  le_antisymm (hz.2 x hx.1) (hx.2 z hz.1)

lemma sc_goldman_tucker {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (hopt : ∃ x : Fin n → ℝ, PrimalOptimal A b c x) :
    ∃ (x : Fin n → ℝ) (y : Fin m → ℝ), PrimalOptimal A b c x ∧ DualOptimal A b c y ∧
      (∀ j, 0 < x j+dualSlack A c y j) ∧ (∀ i, 0 < y i+primalSlack A b x i) := by
  classical
  obtain ⟨x₀,hx₀⟩ := hopt
  obtain ⟨y₀,hy₀,he₀⟩ := strong_duality A b c x₀ hx₀
  let v := c ⬝ᵥ x₀
  let S := sc_optimalPairs A b c v
  have hne : S.Nonempty := ⟨(x₀,y₀),hx₀.1,hy₀.1,rfl,he₀.symm⟩
  have hcoord : ∀ k : Fin n ⊕ Fin m, ∃ p ∈ S, 0 < sc_compCoord A b c k p := by
    intro k
    cases k with
    | inl j =>
      by_cases hj : ∃ x, PrimalOptimal A b c x ∧ 0 < x j
      · obtain ⟨x,hx,hxj⟩ := hj
        refine ⟨(x,y₀),⟨hx.1,hy₀.1,sc_primal_optimal_value hx hx₀,he₀.symm⟩,?_⟩
        change 0 < x j+dualSlack A c y₀ j
        linarith [hy₀.1.2 j]
      · have hzero : ∀ x, PrimalOptimal A b c x → x j=0 := by
          intro x hx
          apply le_antisymm (le_of_not_gt (fun h => hj ⟨x,hx,h⟩))
          exact hx.1.1 j
        obtain ⟨y,hy,hev,hyj⟩ := sc_variable_witness A b c x₀ hx₀ y₀ hy₀.1 he₀.symm j hzero
        refine ⟨(x₀,y),⟨hx₀.1,hy,rfl,hev⟩,?_⟩
        change 0 < x₀ j+dualSlack A c y j
        linarith [hx₀.1.1 j]
    | inr i =>
      by_cases hi : ∃ x, PrimalOptimal A b c x ∧ 0 < primalSlack A b x i
      · obtain ⟨x,hx,hxi⟩ := hi
        refine ⟨(x,y₀),⟨hx.1,hy₀.1,sc_primal_optimal_value hx hx₀,he₀.symm⟩,?_⟩
        change 0 < y₀ i+primalSlack A b x i
        linarith [hy₀.1.1 i]
      · have hzero : ∀ x, PrimalOptimal A b c x → primalSlack A b x i=0 := by
          intro x hx
          apply le_antisymm (le_of_not_gt (fun h => hi ⟨x,hx,h⟩))
          exact hx.1.2 i
        obtain ⟨y,hy,hev,hyi⟩ := sc_slack_witness A b c x₀ hx₀ y₀ hy₀.1 he₀.symm i hzero
        refine ⟨(x₀,y),⟨hx₀.1,hy,rfl,hev⟩,?_⟩
        change 0 < y i+primalSlack A b x₀ i
        linarith [hx₀.1.2 i]
  obtain ⟨p,hp,hpos⟩ := sc_finite_positive S (sc_optimalPairs_convex A b c v) hne
    (sc_compCoord A b c) (sc_compCoord_nonneg A b c v) (sc_compCoord_midpoint A b c) hcoord
  refine ⟨p.1,p.2,⟨hp.1,?_⟩,⟨hp.2.1,?_⟩,fun j => hpos (Sum.inl j),fun i => hpos (Sum.inr i)⟩
  · intro x hx
    have h := hx₀.2 x hx
    rw [hp.2.2.1]
    exact h
  · intro y hy
    rw [hp.2.2.2]
    change c ⬝ᵥ x₀ ≤ b ⬝ᵥ y
    rw [he₀]
    exact hy₀.2 y hy

lemma sc_strictly_complementary_feasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hP : ∃ x : Fin n → ℝ, PrimalFeasible A b x) (hD : ∃ y : Fin m → ℝ, DualFeasible A c y) :
    ∃ (x : Fin n → ℝ) (y : Fin m → ℝ), PrimalFeasible A b x ∧ DualFeasible A c y ∧
      (∀ j, 0 < x j+dualSlack A c y j) ∧ (∀ i, 0 < y i+primalSlack A b x i) := by
  obtain ⟨x₀,hx₀⟩ := hP
  obtain ⟨y₀,hy₀⟩ := hD
  have hopt : ∃ x : Fin n → ℝ, PrimalOptimal A b 0 x :=
    ⟨x₀,hx₀,fun x hx => by simp⟩
  obtain ⟨x,y,hx,hy,hj,hi⟩ := sc_goldman_tucker A b 0 hopt
  have he : dualSlack A c (y+y₀)=dualSlack A 0 y+dualSlack A c y₀ := by
    ext j
    simp only [dualSlack,mulVec_add,Pi.sub_apply,Pi.add_apply,Pi.zero_apply]
    ring
  refine ⟨x,y+y₀,hx.1,⟨fun i => add_nonneg (hy.1.1 i) (hy₀.1 i),fun j => ?_⟩,?_,?_⟩
  · rw [he]; exact add_nonneg (hy.1.2 j) (hy₀.2 j)
  · intro j
    rw [he]
    change 0 < x j+(dualSlack A 0 y j+dualSlack A c y₀ j)
    linarith [hj j,hy₀.2 j]
  · intro i
    change 0 < y i+y₀ i+primalSlack A b x i
    linarith [hi i,hy₀.1 i]

end
end VanderbeiLP.StrictComp

open VanderbeiLP.StrictComp

/-- **Vanderbei, Theorem 10.6 (p. 148).** If both the primal (10.9) and the dual (10.10) have
feasible solutions, then there are a primal feasible `x̄` (slack `w̄ = b - Ax̄`) and a dual
feasible `ȳ` (slack `z̄ = Aᵀȳ - c`) with `x̄ + z̄ > 0` and `ȳ + w̄ > 0` componentwise. -/
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hP : ∃ x : Fin n → ℝ, PrimalFeasible A b x) (hD : ∃ y : Fin m → ℝ, DualFeasible A c y) :
    ∃ (xbar : Fin n → ℝ) (ybar : Fin m → ℝ),
      PrimalFeasible A b xbar ∧ DualFeasible A c ybar ∧
      (∀ j, 0 < xbar j + dualSlack A c ybar j) ∧
      (∀ i, 0 < ybar i + primalSlack A b xbar i) := by
  exact sc_strictly_complementary_feasible A b c hP hD

#print axioms solution
