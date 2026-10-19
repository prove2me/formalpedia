-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSmallSourcePhysicalLoss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/5f31ba38-c25e-4dc2-918c-defbeb39d215

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalPrefactor_smallHazard_twelfthRoot_le
set_option backward.isDefEq.respectTransparency.types false
namespace QuantumParallelRepetition
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
variable {X Y A B : Type*}
namespace Game
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end Game
attribute [instance] Strategy.alice_fintype Strategy.bob_fintype
  Strategy.alice_decidableEq Strategy.bob_decidableEq
namespace Strategy
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}
end Strategy
end
noncomputable section
open scoped BigOperators ComplexConjugate InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Strategy
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}
end Strategy
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
variable {X Y A B : Type*} {J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype J] [DecidableEq J]
variable {G : Game X Y A B}
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open scoped BigOperators
namespace FiniteEventLaw
variable {Ω ι : Type*} [Fintype Ω]
end FiniteEventLaw
section StrategyEventLaw
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end StrategyEventLaw
end
noncomputable section
open scoped BigOperators
variable {ι : Type*}
end
noncomputable section
open scoped BigOperators
end
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Kronecker Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open scoped BigOperators Kronecker
namespace Game
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end Game
section MixedHistories
variable {X Y A B U V : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup V] [Module ℝ V]
end MixedHistories
section RepeatedQuantumFilters
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end RepeatedQuantumFilters
end
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
end
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
end
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 400000
end
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
section ActualHistoryWeights
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end ActualHistoryWeights
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
section HistoryContractions
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end HistoryContractions
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
end
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
end
noncomputable section
open scoped BigOperators
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2048
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3072
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
open WithLp
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 3072
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3072
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3072
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open scoped BigOperators
end
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open scoped BigOperators ComplexOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072
end
noncomputable section
open scoped BigOperators
namespace ClassicalSampling
variable {α : Type*} [Fintype α] [DecidableEq α]
section RationalMarks
variable {β : Type*} [Fintype β] [DecidableEq β]
end RationalMarks
end ClassicalSampling
namespace Pinsker
end Pinsker
namespace ClassicalInformation
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
section CoarseGraining
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
end CoarseGraining
section JointChainRule
variable {κ : Type*} [Fintype κ]
end JointChainRule
section SharedPermutationSampling
end SharedPermutationSampling
end ClassicalInformation
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 3072
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option maxRecDepth 4096
end
noncomputable section
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 3072
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder InnerProductSpace
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 3072
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option maxRecDepth 4096
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open scoped Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
end
noncomputable section
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
end
noncomputable section
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]
end
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
section HistoryNormalization
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end HistoryNormalization
end
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
end
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
section CoordinateWeights
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end CoordinateWeights
end
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology ComplexOrder MatrixOrder
  Matrix.Norms.Elementwise InnerProductSpace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
section CoordinateFilters
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end CoordinateFilters
section ConditionalJensen
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end ConditionalJensen
end
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
section ActualEntropyBudgets
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end ActualEntropyBudgets
end
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
end
noncomputable section
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
section ActualSharedFlag
variable {X Y A B dA dB J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
variable [Fintype J] [DecidableEq J]
end ActualSharedFlag
end
noncomputable section
open Filter
open scoped Topology
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open scoped BigOperators
end
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
section InsertedWeights
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end InsertedWeights
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
section FiniteSamples
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
end FiniteSamples
section ActualRepeatedStrategy
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end ActualRepeatedStrategy
end
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
section ActualFilters
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end ActualFilters
section ActualPurificationHistories
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end ActualPurificationHistories
end
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
section TaggedTensorBlocks
variable {R : Type*} [Fintype R]
variable {ι : R → Type*} [∀ r, Fintype (ι r)]
end TaggedTensorBlocks
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3400000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3400000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open scoped BigOperators
end
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
end
noncomputable section
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
end
noncomputable section
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {Ω T : Type*} [Fintype Ω] [Fintype T] [DecidableEq T]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B dA dB : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 3072
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.Pinsker
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open Filter
open scoped Topology
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
section DependentStoppingBlocks
variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι κ : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
variable [∀ r, Fintype (κ r)] [∀ r, DecidableEq (κ r)]
end DependentStoppingBlocks
end
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
section QuestionLocalStopping
variable {X Y A B R : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype R] [DecidableEq R]
variable {ι : R → Type}
variable [∀ r, Fintype (ι r)] [∀ r, DecidableEq (ι r)]
end QuestionLocalStopping
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open scoped BigOperators
open QuantumParallelRepetition.ClassicalSampling
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
open QuantumParallelRepetition.Pinsker
attribute [local instance] Classical.propDecidable
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
private theorem unconditionalSmallSource_eta_le_one
    (eta alpha : ℝ)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (small : 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1) :
    eta ≤ 1 := by
  have delta_nonnegative : 0 ≤ alpha ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg alpha_positive.le _
  have root_nonnegative := Real.sqrt_nonneg eta
  have root_square := Real.sq_sqrt eta_nonnegative
  nlinarith
private theorem unconditionalSmallSource_eta_scaled_root
    (eta : ℝ) (eta_nonnegative : 0 ≤ eta) :
    eta ^ (1 / 12 : ℝ) ≤ (32 * eta) ^ (1 / 12 : ℝ) := by
  apply Real.rpow_le_rpow eta_nonnegative
  · nlinarith
  · norm_num
private theorem unconditionalSmallSource_root_estimates
    (eta alpha : ℝ)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (small : 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1) :
    let δ := alpha ^ (1 / 3 : ℝ)
    let R := alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)
    0 ≤ R ∧ Real.sqrt eta ≤ R ∧ δ ≤ R ∧ δ ^ 2 ≤ R ∧
      Real.sqrt δ ≤ R := by
  dsimp only
  let δ : ℝ := alpha ^ (1 / 3 : ℝ)
  let R : ℝ :=
    alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)
  have delta_nonnegative : 0 ≤ δ :=
    Real.rpow_nonneg alpha_positive.le _
  have delta_bounded : δ ≤ 1 :=
    Real.rpow_le_one alpha_positive.le alpha_bounded (by norm_num)
  have alpha_root_nonnegative : 0 ≤ alpha ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg alpha_positive.le _
  have scaled_nonnegative : 0 ≤ (32 * eta) ^ (1 / 12 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  have root_nonnegative : 0 ≤ R :=
    add_nonneg alpha_root_nonnegative scaled_nonnegative
  have eta_bounded :=
    unconditionalSmallSource_eta_le_one
      eta alpha eta_nonnegative alpha_positive small
  have eta_scaled :=
    unconditionalSmallSource_eta_scaled_root eta eta_nonnegative
  have eta_root : Real.sqrt eta ≤ eta ^ (1 / 12 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge'
      eta_nonnegative eta_bounded
      (by norm_num : (0 : ℝ) ≤ 1 / 12)
      (by norm_num : (1 / 12 : ℝ) ≤ 1 / 2)
  have eta_bound : Real.sqrt eta ≤ R := by
    dsimp [R]
    linarith
  have delta_root : δ ≤ alpha ^ (1 / 12 : ℝ) := by
    dsimp [δ]
    exact Real.rpow_le_rpow_of_exponent_ge'
      alpha_positive.le alpha_bounded
      (by norm_num : (0 : ℝ) ≤ 1 / 12)
      (by norm_num : (1 / 12 : ℝ) ≤ 1 / 3)
  have delta_bound : δ ≤ R := by
    dsimp [R]
    linarith
  have delta_sq_bound : δ ^ 2 ≤ R := by
    nlinarith [mul_nonneg delta_nonnegative
      (sub_nonneg.mpr delta_bounded)]
  have delta_sqrt_eq : Real.sqrt δ = alpha ^ (1 / 6 : ℝ) := by
    dsimp [δ]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul alpha_positive.le]
    norm_num
  have delta_sqrt_bound : Real.sqrt δ ≤ R := by
    rw [delta_sqrt_eq]
    have root_compare :
        alpha ^ (1 / 6 : ℝ) ≤ alpha ^ (1 / 12 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge'
        alpha_positive.le alpha_bounded
        (by norm_num : (0 : ℝ) ≤ 1 / 12)
        (by norm_num : (1 / 12 : ℝ) ≤ 1 / 6)
    dsimp [R]
    linarith
  exact ⟨root_nonnegative, eta_bound, delta_bound,
    delta_sq_bound, delta_sqrt_bound⟩
private theorem unconditionalSmallSource_clipping_sqrt_le
    (eta alpha clipping : ℝ)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (small : 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1)
    (actual_clipping :
      clipping ≤ 16 * eta + 8 * (3 * alpha ^ (1 / 3 : ℝ) / 2)) :
    Real.sqrt clipping ≤
      8 * (alpha ^ (1 / 12 : ℝ) +
        (32 * eta) ^ (1 / 12 : ℝ)) := by
  let δ : ℝ := alpha ^ (1 / 3 : ℝ)
  let R : ℝ :=
    alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)
  have bounds := unconditionalSmallSource_root_estimates
    eta alpha eta_nonnegative alpha_positive alpha_bounded small
  change 0 ≤ R ∧ Real.sqrt eta ≤ R ∧ δ ≤ R ∧ δ ^ 2 ≤ R ∧
    Real.sqrt δ ≤ R at bounds
  have delta_nonnegative : 0 ≤ δ :=
    Real.rpow_nonneg alpha_positive.le _
  have clip_bound : clipping ≤ 16 * eta + 12 * δ := by
    change clipping ≤ 16 * eta + 8 * (3 * δ / 2)
      at actual_clipping
    nlinarith
  have clip_base_nonnegative : 0 ≤ 16 * eta + 12 * δ := by
    positivity
  have clip_sqrt_base :
      Real.sqrt (16 * eta + 12 * δ) ≤
        4 * Real.sqrt eta + 4 * Real.sqrt δ := by
    have eta_square := Real.sq_sqrt eta_nonnegative
    have delta_square := Real.sq_sqrt delta_nonnegative
    have clip_square := Real.sq_sqrt clip_base_nonnegative
    have cross :=
      mul_nonneg (Real.sqrt_nonneg eta) (Real.sqrt_nonneg δ)
    have clip_root_nonnegative := Real.sqrt_nonneg (16 * eta + 12 * δ)
    have eta_root_nonnegative := Real.sqrt_nonneg eta
    have delta_root_nonnegative := Real.sqrt_nonneg δ
    nlinarith
  change Real.sqrt clipping ≤ 8 * R
  calc
    Real.sqrt clipping ≤ Real.sqrt (16 * eta + 12 * δ) :=
      Real.sqrt_le_sqrt clip_bound
    _ ≤ 4 * Real.sqrt eta + 4 * Real.sqrt δ := clip_sqrt_base
    _ ≤ 8 * R := by linarith [bounds.2.1, bounds.2.2.2.2]
private theorem unconditionalSmallSource_deviation_sqrt_le
    (eta alpha deviation : ℝ)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (small : 64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1)
    (actual_deviation :
      deviation ≤
        (34 / Real.sqrt
            (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) *
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) :
    Real.sqrt deviation ≤
      (4 * Real.sqrt
        (34 + unconditionalPrefactorBucketCoefficient) + 2) *
        (alpha ^ (1 / 12 : ℝ) +
          (32 * eta) ^ (1 / 12 : ℝ)) := by
  let k : ℝ :=
    4 * Real.sqrt (34 + unconditionalPrefactorBucketCoefficient) + 2
  let R : ℝ :=
    alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)
  have k_nonnegative : 0 ≤ k := by
    dsimp [k]
    positivity
  have scaled :=
    unconditionalSmallSource_eta_scaled_root eta eta_nonnegative
  have envelope := unconditionalPrefactor_smallHazard_twelfthRoot_le
    eta_nonnegative alpha_positive small
  change Real.sqrt deviation ≤ k * R
  calc
    Real.sqrt deviation ≤
        Real.sqrt
          ((34 / Real.sqrt
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) *
                (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) +
            4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
            unconditionalPrefactorBucketCoefficient *
              Real.sqrt
                (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) :=
      Real.sqrt_le_sqrt actual_deviation
    _ ≤ k * (eta ^ (1 / 12 : ℝ) +
        alpha ^ (1 / 12 : ℝ)) := by
      simpa [k] using envelope
    _ ≤ k * R := by
      apply mul_le_mul_of_nonneg_left _ k_nonnegative
      dsimp [R]
      linarith
end
noncomputable section
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
end
noncomputable section
end
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
namespace UnconditionalActualFairSourceRoundingContext
variable {X Y A B : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B} {n : ℕ} {S : Strategy (G.repeat n)}
variable {D : Finset (Fin n)} {alpha gamma : ℝ}
end UnconditionalActualFairSourceRoundingContext
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
open UnconditionalActualFairSourceRoundingContext
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
attribute [local instance] Classical.propDecidable
end
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
end
noncomputable section
end
end QuantumParallelRepetition
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
namespace QuantumParallelRepetition
theorem _root_.solution
    (K eta alpha deviation clipping : ℝ)
    (constant :
      1024 + 8 *
          (4 * Real.sqrt
            (34 + unconditionalPrefactorBucketCoefficient) + 2) ≤ K)
    (eta_nonnegative : 0 ≤ eta)
    (alpha_positive : 0 < alpha)
    (alpha_bounded : alpha ≤ 1)
    (small :
      64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) ≤ 1)
    (actual_deviation :
      deviation ≤
        (34 / Real.sqrt
            (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ))) *
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)) +
          4 * (alpha ^ (1 / 12 : ℝ)) ^ 2 +
          unconditionalPrefactorBucketCoefficient *
            Real.sqrt
              (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ)))
    (actual_clipping :
      clipping ≤
        16 * eta + 8 * (3 * alpha ^ (1 / 3 : ℝ) / 2)) :
    (64 * Real.sqrt eta + alpha ^ (1 / 3 : ℝ) +
        (alpha ^ (1 / 3 : ℝ)) ^ 2) +
      4 * Real.sqrt deviation + 4 * Real.sqrt clipping ≤
        K * (alpha ^ (1 / 12 : ℝ) +
          (32 * eta) ^ (1 / 12 : ℝ)) := by
  let δ : ℝ := alpha ^ (1 / 3 : ℝ)
  let R : ℝ :=
    alpha ^ (1 / 12 : ℝ) + (32 * eta) ^ (1 / 12 : ℝ)
  let k : ℝ :=
    4 * Real.sqrt (34 + unconditionalPrefactorBucketCoefficient) + 2
  have bounds := unconditionalSmallSource_root_estimates
    eta alpha eta_nonnegative alpha_positive alpha_bounded small
  change 0 ≤ R ∧ Real.sqrt eta ≤ R ∧ δ ≤ R ∧ δ ^ 2 ≤ R ∧
    Real.sqrt δ ≤ R at bounds
  have R_nonnegative := bounds.1
  have eta_sqrt_le_R := bounds.2.1
  have delta_le_R := bounds.2.2.1
  have delta_sq_le_R := bounds.2.2.2.1
  have clip_sqrt_le :=
    unconditionalSmallSource_clipping_sqrt_le
      eta alpha clipping eta_nonnegative alpha_positive alpha_bounded
      small actual_clipping
  change Real.sqrt clipping ≤ 8 * R at clip_sqrt_le
  have k_nonnegative : 0 ≤ k := by
    dsimp [k]
    positivity
  have deviation_sqrt_le :=
    unconditionalSmallSource_deviation_sqrt_le
      eta alpha deviation eta_nonnegative alpha_positive small
      actual_deviation
  change Real.sqrt deviation ≤ k * R at deviation_sqrt_le
  have source_loss :
      64 * Real.sqrt eta + δ + δ ^ 2 ≤ 66 * R := by
    nlinarith
  change
    (64 * Real.sqrt eta + δ + δ ^ 2) +
      4 * Real.sqrt deviation + 4 * Real.sqrt clipping ≤ K * R
  calc
    (64 * Real.sqrt eta + δ + δ ^ 2) +
        4 * Real.sqrt deviation + 4 * Real.sqrt clipping ≤
      66 * R + 4 * (k * R) + 4 * (8 * R) := by
        linarith
    _ ≤ (1024 + 8 * k) * R := by
      nlinarith [mul_nonneg k_nonnegative R_nonnegative]
    _ ≤ K * R := by
      apply mul_le_mul_of_nonneg_right _ R_nonnegative
      simpa [k] using constant
end QuantumParallelRepetition
